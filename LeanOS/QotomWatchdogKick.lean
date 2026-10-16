/-!
# Watchdog kicks for long Qotom WiFi sessions (issue #557)

The Qotom lab flow boots LeanOS under the Bay Trail TCO watchdog: GRUB arms
it for 120 one-second ticks after checking the board and every register it
touches (`hardware/lab/grub-qotom-watchdog.cfg`, `docs/qotom-watchdog-lab.md`),
and if LeanOS hangs the timer resets the board, which returns to FreeBSD.
The WiFi join takes about 55 seconds, so a session can serve frames for
about 45 seconds before the reset. An access point rotates its group key on
a much longer interval (often an hour), so observing a rekey needs a longer
session.

A long session (`build-qotom-recovery-lab.py --long-session SECONDS`) lets
the lab kernel **reload** the running timer, never reprogram it, while the
WiFi driver subject makes progress. The kernel asks this check before each
reload, on two kinds of driver record:

* the **link record** (event 1), the link-only endpoint's first record: the
  join and the 4-way handshake completed;
* a **tick** (event 2), which the endpoint yields once per second of the
  radio's TSF time (`LeanOS.Wifi.Endpoint.serveLink`); a tick reaches the
  kernel only when the driver program yielded it and the ring-3 subject
  took the previous record.

`kickDecide` admits a reload (0) only if all of these hold, and otherwise
names the first that fails:

* the session's kick budget is between 1 and `capKicks` (the budget of a
  one-hour session), and fewer kicks than the budget have been made;
* the timer is still exactly as GRUB armed it: TCO1_CNT reads 0 (running,
  not halted) and TCO_TMR reads 120;
* the event is the link record and nothing was kicked yet, or a tick after
  at least `kickPeriod` (40) ticks since the last kick.

What is proved:

* `kickDecide_zero_iff`: the conditions above, exactly.
* `run_kicks_le_budget`, `run_kicks_le_cap`: however the driver behaves,
  a session reloads the timer at most its budget times, and never more than
  `capKicks` (92) times.
* `kick_needs_ticks`: every reload but the link record's follows at least
  40 ticks, so reloads are at least 40 seconds of TSF time apart.
* `unarmed_never_kicked`, `changed_never_kicked`: a timer GRUB did not
  arm, or one whose timeout changed, is never reloaded.
* `deadline_le`, `reset_bound`: if every reload comes before the running
  deadline, the board resets at most `(n + 1) · 120` seconds after GRUB's
  arm when `n` reloads were made, so no later than
  `(budget + 1) · 120` seconds; for a one-hour budget that is
  `(capKicks + 1) · 120 = 11160` seconds (`cap_reset_seconds`), and
  `budgetOf 1800 = 47` gives 5760 seconds (`budget_1800`).

## Ending the session within its budget (issue #567)

The serve window is measured in the radio's TSF time, and the TSF is the
access point's clock: the station adopts the timestamps of its beacons, so
neither the window nor the tick rate is under LeanOS's control. A session
that kept making progress once yielded more ticks than its budget covers,
and the budget ran out before the driver program reached its end: the board
reset as proved, but the session never printed `FINAL`.

So the kernel ends the session itself once the budget is spent. Before it
resumes the driver program for the next record it asks `endDecide`, which
answers 1 (end now) when the budget is invalid or every reload in it has
been made, and 0 (serve on) otherwise. On 1 the kernel resumes the driver
no more, prints `FINAL ... session-end=budget` and halts, inside the 120
seconds the last reload gave it; the board then resets.

What is proved:

* `endDecide_zero_iff`: the session is served on exactly while the budget is
  valid and not spent.
* `serving_never_exhausted`: while the session is served, the kick check
  never refuses for a spent (`exhausted`) or an invalid budget.
* `asked_never_exhausted`: however the driver behaves, no kick decision the
  kernel asks in a session (`serve`, `asked`) is `exhausted` or
  `badBudget`, so the budget never runs out under a session still served.
* `serve_spent_ends`: once the last reload is made, the very next kernel
  turn ends the session: no further record is taken, nothing is reloaded.
* `serve_budget_end_spent`: a session ends at its budget only with every
  reload of a valid budget made; `serve_kicks_le_budget` and
  `serve_kicks_le_cap` keep every session within its budget and within
  `capKicks` reloads, so `reset_bound` and `cap_reset_seconds` still bound
  the reset.

The budget, the cap and the reset bound are unchanged: the change only puts
`FINAL` before the budget runs out.

The decisions are exported as `leanos_qotom_watchdog_kick` and
`leanos_qotom_watchdog_session_end`, linked into the freestanding
`native-pci.o` of the lab image; their arguments and results are fixed-width
`UInt64` and they allocate nothing. The lab kernel's reads of TCO1_CNT and
TCO_TMR, its one reload write (TCO_RLD, as FreeBSD's `ichwd` reloads), its
event classification and the way it ends the session are C, reviewed and
not proved.
-/

namespace LeanOS.QotomWatchdogKick

/-- The timeout GRUB arms, in TCO v3 one-second ticks. -/
def timeoutTicks : Nat := 120
/-- Ticks between reloads: a third of the timeout. -/
def kickPeriod : Nat := 40
/-- The longest session a lab image may request, in seconds. -/
def maxSessionSeconds : Nat := 3600

/-- The kick budget of a session of `seconds`: one for the link record, one
per `kickPeriod` ticks of the serve window, and one spare. -/
def budgetOf (seconds : Nat) : Nat := 2 + (seconds + kickPeriod - 1) / kickPeriod

/-- The largest budget: a one-hour session's. -/
def capKicks : Nat := budgetOf maxSessionSeconds

theorem capKicks_eq : capKicks = 92 := by decide

theorem budget_1800 : budgetOf 1800 = 47 := by decide

theorem budgetOf_le_cap (seconds : Nat) (h : seconds ≤ maxSessionSeconds) :
    budgetOf seconds ≤ capKicks := by
  unfold capKicks budgetOf maxSessionSeconds kickPeriod at *
  have : (seconds + 40 - 1) / 40 ≤ (3600 + 40 - 1) / 40 := Nat.div_le_div_right (by omega)
  omega

/-! ## The decision -/

namespace Reason
def kick : UInt64 := 0
def notDue : UInt64 := 1
def exhausted : UInt64 := 2
def badBudget : UInt64 := 3
def notArmed : UInt64 := 4
def timeoutChanged : UInt64 := 5
def badEvent : UInt64 := 6
end Reason

/-- Events: the link record and a tick. -/
def linkEvent : UInt64 := 1
def tickEvent : UInt64 := 2

/-- Should the kernel reload the timer now? `ticks` counts ticks since the
last reload (including this one), `kicks` the reloads made, `budget` the
session's budget, `count` and `timer` the TCO1_CNT and TCO_TMR words just
read. 0 reloads; anything else is the reason not to. -/
def kickDecide (event ticks kicks budget count timer : UInt64) : UInt64 :=
  if budget = 0 ∨ budget > 92 then Reason.badBudget
  else if kicks ≥ budget then Reason.exhausted
  else if count ≠ 0 then Reason.notArmed
  else if timer ≠ 120 then Reason.timeoutChanged
  else if event = linkEvent then (if kicks = 0 then Reason.kick else Reason.notDue)
  else if event = tickEvent then
    (if ticks ≥ 40 then Reason.kick else Reason.notDue)
  else Reason.badEvent

/-- The literals of `kickDecide` are `capKicks` and `kickPeriod` (literals keep
the exported code free of Nat arithmetic and lazily initialised constants). -/
theorem budget_le_iff (budget : UInt64) : ¬ (budget > 92) ↔ budget.toNat ≤ capKicks := by
  rw [capKicks_eq, GT.gt, UInt64.lt_iff_toNat_lt]
  show ¬ (92 < budget.toNat) ↔ budget.toNat ≤ 92
  omega

theorem ticks_ge_iff (ticks : UInt64) : ticks ≥ 40 ↔ kickPeriod ≤ ticks.toNat := by
  rw [GE.ge, UInt64.le_iff_toNat_le]
  show 40 ≤ ticks.toNat ↔ 40 ≤ ticks.toNat
  exact Iff.rfl

/-- The exported check, called by the lab kernel before every reload. -/
@[export leanos_qotom_watchdog_kick]
def exportedKick (event ticks kicks budget count timer : UInt64) : UInt64 :=
  kickDecide event ticks kicks budget count timer

theorem kickDecide_zero_iff (event ticks kicks budget count timer : UInt64) :
    kickDecide event ticks kicks budget count timer = 0 ↔
      (budget ≠ 0 ∧ budget.toNat ≤ capKicks) ∧ kicks < budget ∧ count = 0 ∧ timer = 120 ∧
        ((event = linkEvent ∧ kicks = 0) ∨ (event = tickEvent ∧ kickPeriod ≤ ticks.toNat)) := by
  unfold kickDecide
  simp only [Reason.kick, Reason.notDue, Reason.exhausted, Reason.badBudget, Reason.notArmed,
    Reason.timeoutChanged, Reason.badEvent, linkEvent, tickEvent]
  constructor
  · intro h
    split at h
    · exact absurd h (by decide)
    · rename_i h1
      split at h
      · exact absurd h (by decide)
      · rename_i h2
        split at h
        · exact absurd h (by decide)
        · rename_i h3
          split at h
          · exact absurd h (by decide)
          · rename_i h4
            simp only [not_or] at h1
            have h1 : ¬budget = 0 ∧ budget.toNat ≤ capKicks := ⟨h1.1, (budget_le_iff _).mp h1.2⟩
            simp only [ne_eq, Decidable.not_not] at h3 h4
            refine ⟨⟨h1.1, h1.2⟩, UInt64.not_le.mp h2, h3, h4, ?_⟩
            by_cases h5 : event = 1
            · simp only [h5, ↓reduceIte] at h
              by_cases h6 : kicks = 0
              · exact Or.inl ⟨h5, h6⟩
              · simp only [h6, ↓reduceIte] at h; exact absurd h (by decide)
            · simp only [h5, ↓reduceIte] at h
              by_cases h6 : event = 2
              · simp only [h6, ↓reduceIte] at h
                by_cases h7 : ticks ≥ 40
                · exact Or.inr ⟨h6, (ticks_ge_iff _).mp h7⟩
                · simp only [h7, ↓reduceIte] at h; exact absurd h (by decide)
              · simp only [h6, ↓reduceIte] at h; exact absurd h (by decide)
  · intro ⟨⟨hb0, hbc⟩, hk, hc, ht, he⟩
    have h1 : ¬(budget = 0 ∨ budget > 92) :=
      fun h => h.elim hb0 ((budget_le_iff _).mpr hbc)
    have h2 : ¬(kicks ≥ budget) := UInt64.not_le.mpr hk
    simp only [h1, h2, hc, ht, ne_eq, not_true_eq_false, ↓reduceIte]
    rcases he with ⟨he, hk0⟩ | ⟨he, ht'⟩
    · simp only [he, hk0, ↓reduceIte]
    · have h21 : ¬ ((2 : UInt64) = 1) := by decide
      have ht40 : ticks ≥ 40 := (ticks_ge_iff _).mpr ht'
      simp only [he, h21, ↓reduceIte, ht40]

/-- A timer GRUB did not arm (TCO1_CNT not 0: halted, or changed) is never
reloaded. -/
theorem unarmed_never_kicked (event ticks kicks budget count timer : UInt64) (h : count ≠ 0) :
    kickDecide event ticks kicks budget count timer ≠ 0 := by
  intro hz
  exact h ((kickDecide_zero_iff _ _ _ _ _ _).mp hz).2.2.1

/-- A timer whose timeout is no longer GRUB's 120 ticks is never reloaded. -/
theorem changed_never_kicked (event ticks kicks budget count timer : UInt64) (h : timer ≠ 120) :
    kickDecide event ticks kicks budget count timer ≠ 0 := by
  intro hz
  exact h ((kickDecide_zero_iff _ _ _ _ _ _).mp hz).2.2.2.1

/-! ## The kernel's kick state across a session -/

/-- What the lab kernel keeps: ticks since the last reload and reloads. -/
structure State where
  ticks : Nat
  kicks : Nat
  deriving DecidableEq, Repr

/-- What the kernel reads before a decision. -/
structure Reading where
  event : UInt64
  count : UInt64
  timer : UInt64

/-- One driver record: count a tick, ask the check, and reload on 0. The
counters are 64-bit words in the kernel; a session never comes near their
range (`run_kicks_le_cap`). -/
def tickCount (s : State) (r : Reading) : Nat :=
  if r.event = tickEvent then s.ticks + 1 else s.ticks

def step (budget : UInt64) (s : State) (r : Reading) : State × Bool :=
  if kickDecide r.event (tickCount s r).toUInt64 s.kicks.toUInt64 budget r.count r.timer = 0 then
    ({ ticks := 0, kicks := s.kicks + 1 }, true)
  else ({ s with ticks := tickCount s r }, false)

def run (budget : UInt64) : State → List Reading → State
  | s, [] => s
  | s, r :: rs => run budget (step budget s r).1 rs

/-- A step reloads only within the budget. -/
theorem step_kicks (budget : UInt64) (s : State) (r : Reading) (hs : s.kicks ≤ budget.toNat) :
    (step budget s r).1.kicks ≤ budget.toNat := by
  unfold step
  split
  · rename_i h
    obtain ⟨⟨-, hcap⟩, hk, -⟩ := (kickDecide_zero_iff _ _ _ _ _ _).mp h
    have hk' := UInt64.lt_iff_toNat_lt.mp hk
    have hsmall : s.kicks < 2 ^ 64 := by
      unfold capKicks budgetOf maxSessionSeconds kickPeriod at hcap; omega
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsmall] at hk'
    show s.kicks + 1 ≤ budget.toNat
    omega
  · exact hs

/-- However the driver behaves, a session reloads the timer at most its
budget times. -/
theorem run_kicks_le_budget (budget : UInt64) (s : State) (rs : List Reading)
    (hs : s.kicks ≤ budget.toNat) : (run budget s rs).kicks ≤ budget.toNat := by
  induction rs generalizing s with
  | nil => exact hs
  | cons r rs ih => exact ih _ (step_kicks budget s r hs)

/-- The kick count only grows. -/
theorem step_kicks_mono (budget : UInt64) (s : State) (r : Reading) :
    s.kicks ≤ (step budget s r).1.kicks := by
  unfold step
  split
  · show s.kicks ≤ s.kicks + 1; omega
  · exact Nat.le_refl _

/-- Whatever budget an image declares, a session from the start reloads the
timer at most `capKicks` times: a larger budget is refused outright. -/
theorem run_kicks_le_cap (budget : UInt64) (rs : List Reading) :
    (run budget ⟨0, 0⟩ rs).kicks ≤ capKicks := by
  by_cases hb : budget.toNat ≤ capKicks
  · exact Nat.le_trans (run_kicks_le_budget budget ⟨0, 0⟩ rs (Nat.zero_le _)) hb
  · -- every decision is `badBudget`, so nothing is ever reloaded
    have : ∀ s r, (step budget s r).1.kicks = s.kicks := by
      intro s r
      unfold step
      split
      · rename_i h
        exact absurd ((kickDecide_zero_iff _ _ _ _ _ _).mp h).1.2 hb
      · rfl
    have hrun : ∀ (s : State) rs, (run budget s rs).kicks = s.kicks := by
      intro s rs
      induction rs generalizing s with
      | nil => rfl
      | cons r rs ih => simp only [run]; rw [ih, this]
    rw [hrun]; exact Nat.zero_le _

/-- Every reload but the link record's follows at least `kickPeriod` ticks
since the previous one. -/
theorem kick_needs_ticks (budget : UInt64) (s : State) (r : Reading)
    (h : (step budget s r).2 = true) (hr : r.event ≠ linkEvent) :
    kickPeriod ≤ (tickCount s r).toUInt64.toNat := by
  unfold step at h
  split at h
  · rename_i hz
    obtain ⟨-, -, -, -, he⟩ := (kickDecide_zero_iff _ _ _ _ _ _).mp hz
    rcases he with ⟨he, _⟩ | ⟨_, ht⟩
    · exact absurd he hr
    · exact ht
  · cases h

/-! ## When the board resets -/

/-- The running deadline, in seconds after GRUB's arm, after reloads at
times `ts` (in order): each reload restarts the 120-second countdown. -/
def deadline : List Nat → Nat
  | [] => timeoutTicks
  | ts => ts.getLast?.getD 0 + timeoutTicks

/-- The reloads happen in time: each before the deadline then running. -/
def InTime : Nat → List Nat → Prop
  | _, [] => True
  | d, t :: ts => t < d ∧ InTime (t + timeoutTicks) ts

/-- Reloads that each come before the running deadline `d` leave the last
one's deadline at most `d` plus 120 seconds per reload. -/
theorem deadline_le (d : Nat) (ts : List Nat) (h : InTime d ts) (hne : ts ≠ []) :
    ts.getLast?.getD 0 + timeoutTicks ≤ d + ts.length * timeoutTicks := by
  induction ts generalizing d with
  | nil => exact absurd rfl hne
  | cons t rest ih =>
    obtain ⟨ht, hrest⟩ := h
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.getD_some, List.length_cons, List.length_nil]
      unfold timeoutTicks; omega
    | cons u us =>
      have := ih (t + timeoutTicks) hrest (List.cons_ne_nil _ _)
      rw [List.getLast?_cons_cons]
      simp only [List.length_cons] at this ⊢
      unfold timeoutTicks at *; omega

/-- From GRUB's arm (deadline 120), `n` in-time reloads leave the board
resetting at most `(n + 1) · 120` seconds after the arm. -/
theorem reset_bound (ts : List Nat) (h : InTime timeoutTicks ts) :
    deadline ts ≤ (ts.length + 1) * timeoutTicks := by
  cases ts with
  | nil => simp [deadline]
  | cons t rest =>
    have := deadline_le timeoutTicks (t :: rest) h (List.cons_ne_nil _ _)
    unfold deadline
    simp only [List.length_cons] at this ⊢
    unfold timeoutTicks at *; omega

/-- With the largest budget the board resets at most 11160 seconds (3 h
6 min) after GRUB's arm; with a 30-minute session's, 5760 seconds. -/
theorem cap_reset_seconds : (capKicks + 1) * timeoutTicks = 11160 := by decide

theorem session_1800_reset_seconds : (budgetOf 1800 + 1) * timeoutTicks = 5760 := by decide

/-! ## Ending the session within its budget (issue #567) -/

/-- Should the kernel end the session now, instead of resuming the driver
program for its next record? 1 ends it (the budget is invalid, or every
reload in it was made); 0 serves on. -/
def endDecide (kicks budget : UInt64) : UInt64 :=
  if budget = 0 ∨ budget > 92 then 1
  else if kicks ≥ budget then 1
  else 0

/-- The exported check, called by the lab kernel before it resumes the driver
program. -/
@[export leanos_qotom_watchdog_session_end]
def exportedSessionEnd (kicks budget : UInt64) : UInt64 :=
  endDecide kicks budget

theorem endDecide_zero_iff (kicks budget : UInt64) :
    endDecide kicks budget = 0 ↔ (budget ≠ 0 ∧ budget.toNat ≤ capKicks) ∧ kicks < budget := by
  unfold endDecide
  constructor
  · intro h
    split at h
    · exact absurd h (by decide)
    · rename_i h1
      split at h
      · exact absurd h (by decide)
      · rename_i h2
        simp only [not_or] at h1
        exact ⟨⟨h1.1, (budget_le_iff _).mp h1.2⟩, UInt64.not_le.mp h2⟩
  · intro ⟨⟨hb0, hbc⟩, hk⟩
    have h1 : ¬(budget = 0 ∨ budget > 92) :=
      fun h => h.elim hb0 ((budget_le_iff _).mpr hbc)
    have h2 : ¬(kicks ≥ budget) := UInt64.not_le.mpr hk
    simp only [h1, h2, ↓reduceIte]

/-- The check answers only 0 or 1. -/
theorem endDecide_cases (kicks budget : UInt64) :
    endDecide kicks budget = 0 ∨ endDecide kicks budget = 1 := by
  unfold endDecide
  split
  · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- While the session is served, the kick check never refuses for a spent or
an invalid budget. -/
theorem serving_never_exhausted (event ticks kicks budget count timer : UInt64)
    (h : endDecide kicks budget = 0) :
    kickDecide event ticks kicks budget count timer ≠ Reason.exhausted ∧
      kickDecide event ticks kicks budget count timer ≠ Reason.badBudget := by
  obtain ⟨⟨hb0, hbc⟩, hk⟩ := (endDecide_zero_iff _ _).mp h
  have h1 : ¬(budget = 0 ∨ budget > 92) :=
    fun h => h.elim hb0 ((budget_le_iff _).mpr hbc)
  have h2 : ¬(kicks ≥ budget) := UInt64.not_le.mpr hk
  unfold kickDecide
  simp only [h1, h2, ↓reduceIte, Reason.exhausted, Reason.badBudget, Reason.kick, Reason.notDue,
    Reason.notArmed, Reason.timeoutChanged, Reason.badEvent]
  constructor <;>
    (repeat' split) <;> decide

/-- A session as the lab kernel serves it: before each record it asks
`endDecide`; on 1 it ends the session (`FINAL ... session-end=budget`) and
takes no further record; on 0 the driver yields the record and the kernel
steps. The result is the final state and whether the session ended at its
budget; a session whose records run out ended at its serve window (the
driver program halted). -/
def serve (budget : UInt64) : State → List Reading → State × Bool
  | s, [] => (s, false)
  | s, r :: rs =>
    if endDecide s.kicks.toUInt64 budget ≠ 0 then (s, true)
    else serve budget (step budget s r).1 rs

/-- The kick decisions the kernel asks in such a session, in order. -/
def asked (budget : UInt64) : State → List Reading → List UInt64
  | _, [] => []
  | s, r :: rs =>
    if endDecide s.kicks.toUInt64 budget ≠ 0 then []
    else kickDecide r.event (tickCount s r).toUInt64 s.kicks.toUInt64 budget r.count r.timer ::
      asked budget (step budget s r).1 rs

/-- However the driver behaves, no kick decision asked in a session is
`exhausted` or `badBudget`: the budget never runs out under a session that
is still served, so `FINAL` comes before any such refusal. -/
theorem asked_never_exhausted (budget : UInt64) (s : State) (rs : List Reading) :
    ∀ d ∈ asked budget s rs, d ≠ Reason.exhausted ∧ d ≠ Reason.badBudget := by
  induction rs generalizing s with
  | nil => intro d hd; cases hd
  | cons r rs ih =>
    intro d hd
    unfold asked at hd
    split at hd
    · cases hd
    · rename_i h
      rcases List.mem_cons.mp hd with rfl | hd
      · exact serving_never_exhausted _ _ _ _ _ _ (Decidable.not_not.mp h)
      · exact ih _ d hd

/-- Once the last reload is made, the next kernel turn ends the session: no
record is taken and nothing more is reloaded. -/
theorem serve_spent_ends (budget : UInt64) (s : State) (r : Reading) (rs : List Reading)
    (hspent : s.kicks = budget.toNat) : serve budget s (r :: rs) = (s, true) := by
  have hk : ¬(s.kicks.toUInt64 < budget) := by
    rw [hspent, Nat.toUInt64_eq, UInt64.ofNat_toNat]
    exact UInt64.lt_irrefl _
  have h : endDecide s.kicks.toUInt64 budget ≠ 0 := fun h =>
    hk ((endDecide_zero_iff _ _).mp h).2
  simp only [serve, h, ne_eq, not_false_eq_true, ↓reduceIte]

/-- A session reloads the timer at most its budget times. -/
theorem serve_kicks_le_budget (budget : UInt64) (s : State) (rs : List Reading)
    (hs : s.kicks ≤ budget.toNat) : (serve budget s rs).1.kicks ≤ budget.toNat := by
  induction rs generalizing s with
  | nil => exact hs
  | cons r rs ih =>
    simp only [serve]
    split
    · exact hs
    · exact ih _ (step_kicks budget s r hs)

/-- The state a session ends in is one a run over some of its records
reaches. -/
theorem serve_is_run (budget : UInt64) (s : State) (rs : List Reading) :
    ∃ qs, (serve budget s rs).1 = run budget s qs := by
  induction rs generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons r rs ih =>
    simp only [serve]
    split
    · exact ⟨[], rfl⟩
    · obtain ⟨qs, hq⟩ := ih (step budget s r).1
      exact ⟨r :: qs, hq⟩

/-- Whatever budget an image declares, a session from the start reloads the
timer at most `capKicks` times, so `reset_bound` and `cap_reset_seconds`
still bound its reset. -/
theorem serve_kicks_le_cap (budget : UInt64) (rs : List Reading) :
    (serve budget ⟨0, 0⟩ rs).1.kicks ≤ capKicks := by
  obtain ⟨qs, hq⟩ := serve_is_run budget ⟨0, 0⟩ rs
  rw [hq]
  exact run_kicks_le_cap budget qs

/-- With a valid budget, a session ends at its budget only once every reload
in it was made. -/
theorem serve_budget_end_spent (budget : UInt64) (hb0 : budget ≠ 0)
    (hbc : budget.toNat ≤ capKicks) (s : State) (rs : List Reading)
    (hs : s.kicks ≤ budget.toNat) (hend : (serve budget s rs).2 = true) :
    (serve budget s rs).1.kicks = budget.toNat := by
  induction rs generalizing s with
  | nil => simp [serve] at hend
  | cons r rs ih =>
    simp only [serve] at hend ⊢
    split at hend
    · rename_i h
      simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
      have hsmall : s.kicks.toUInt64.toNat = s.kicks := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        unfold capKicks budgetOf maxSessionSeconds kickPeriod at hbc; omega
      have : ¬(s.kicks.toUInt64 < budget) := fun hk =>
        h ((endDecide_zero_iff _ _).mpr ⟨⟨hb0, hbc⟩, hk⟩)
      rw [UInt64.lt_iff_toNat_lt, hsmall] at this
      show s.kicks = budget.toNat
      omega
    · rename_i h
      simp only [h, ↓reduceIte]
      exact ih _ (step_kicks budget s r hs) hend

end LeanOS.QotomWatchdogKick
