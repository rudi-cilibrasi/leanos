/-!
# Timer server over the one-shot PIT (issue #487)

The kernel keeps the PIT and its interrupt. Alarm policy lives in a ring-3
timer server. This module models the split.

* **The timer capability.** At most one subject holds it (`timerHolder`). It
  is the authority to ask the kernel for one bounded one-shot alarm (`arm`):
  a count in `1 .. maxCount`, the range of the 16-bit channel-0 counter
  without the hardware's "0 means 65536". The kernel refuses an arm from any
  other subject, and an arm outside the bound, without effect
  (`arm_non_holder_unchanged`, `arm_out_of_bound_unchanged`). No other
  operation sets the alarm (`alarm_set_only_by_holder`).
* **The kernel multiplexes the PIT.** The PIT state holds the kernel's own
  preemption deadline next to the server's alarm, and the kernel programs the
  earlier of the two (`Pit.programmed`). No operation changes the preemption
  deadline (`preemption_unchanged`), so the server cannot disable or delay the
  preemption tick (`programmed_le_preemption`, `tick_independent_of_alarm`).
* **Expiry.** When the alarm fires, the kernel's interrupt path clears the
  alarm and signals the expiry notification bound to the timer-capability
  holder, and nothing else: it touches no server state, no client, no
  authority, and not the preemption deadline (`expire_footprint`). Only the
  holder ever has pending expiry bits (`ExpiryBound`, preserved by every
  step).
* **Clients and policy.** A client reaches the server only through a
  send-only endpoint capability (`reachesServer`). A request from a subject
  without it is refused by the kernel without effect
  (`request_without_endpoint_unchanged`), so every queued alarm, the only
  thing the server arms, belongs to a subject holding the endpoint
  (`QueueFromSenders`). The server's policy (`policy`) refuses a count
  outside the bound and a request that would exceed the client's quota of
  outstanding alarms, so no client's outstanding count ever exceeds the quota
  (`WithinQuota`, preserved by every step).
* **Wakes.** Only the holder, taking its expiry bits (`collect`), signals a
  client's wake notification, and only the client at the head of its queue.

The model has no time: counts are bounds on the hardware counter, not claims
about wall-clock accuracy, latency, or timing channels.

The allocation-free boot witness `timerServerDecide` is tied to `step` on the
image's boot system by `timerServerDecide_agrees`.
-/
namespace LeanOS.TimerServer

abbrev SubjectId := Nat

/-- The largest one-shot count: the PIT channel-0 counter is 16 bits wide,
and the hardware reads 0 as 65536, which the bound excludes. -/
def maxCount : Nat := 65535

/-- A count the kernel will program. -/
def InBound (count : Nat) : Bool := 1 ≤ count && count ≤ maxCount

/-- Static authority installed at boot. This slice has no capability
transfer for the timer capability or the server endpoint. -/
structure Authority where
  /-- The one subject holding the timer capability, if any. It is also the
  server: the receiver of the server endpoint and the only subject allowed
  to signal client wake notifications. -/
  timerHolder : Option SubjectId
  /-- Subjects holding a send-only endpoint capability to the server. -/
  reachesServer : SubjectId → Bool

/-- The kernel-owned PIT channel 0, multiplexed between the kernel's
preemption deadline and the server's one alarm. -/
structure Pit where
  /-- The kernel's preemption deadline (ADR 0008); only the kernel sets it. -/
  preemption : Option Nat
  /-- The server's one outstanding alarm. -/
  alarm : Option Nat
  deriving DecidableEq, Repr

/-- The count the kernel programs: the earlier of the two deadlines. -/
def Pit.programmed (pit : Pit) : Option Nat :=
  match pit.preemption, pit.alarm with
  | some p, some a => some (min p a)
  | some p, none => some p
  | none, a => a

/-- The ring-3 server's policy state. -/
structure Server where
  /-- At most this many outstanding alarms per client. -/
  quota : Nat
  outstanding : SubjectId → Nat
  /-- Accepted alarms in order: (client, count). The head is the armed one. -/
  queue : List (SubjectId × Nat)

structure System where
  auth : Authority
  pit : Pit
  /-- Pending bits on each subject's bound expiry notification. -/
  expiries : SubjectId → Nat
  server : Server
  /-- Pending bits on each client's wake notification. -/
  wakes : SubjectId → Nat
  /-- Preemption ticks the kernel accepted. -/
  ticks : Nat

inductive Op where
  /-- A subject asks the kernel to arm the one-shot alarm. -/
  | arm (actor : SubjectId) (count : Nat)
  /-- A client sends an alarm request to the server's endpoint; the server
  runs its policy on the message. -/
  | request (client : SubjectId) (count : Nat)
  /-- The holder takes its expiry bits and wakes the client at the head of
  its queue. -/
  | collect (actor : SubjectId)
  /-- A subject takes its own wake bits. -/
  | wait (subject : SubjectId)
  /-- The PIT alarm interrupt (kernel path). -/
  | expire
  /-- The kernel's preemption tick (kernel path). -/
  | tick
  deriving DecidableEq, Repr

inductive Refusal where
  | noTimerCapability
  | outOfBound
  | noEndpoint
  | quotaExceeded
  | notHolder
  | nothingPending
  | notArmed
  deriving DecidableEq, Repr

inductive Reply where
  | armed (count : Nat)
  | accepted (client : SubjectId)
  | refused (reason : Refusal)
  | delivered (holder : SubjectId)
  | woke (client : SubjectId)
  | took (bits : Nat)
  | ticked
  deriving DecidableEq, Repr

def bump (f : SubjectId → Nat) (s : SubjectId) : SubjectId → Nat :=
  fun t => if t = s then f t + 1 else f t

def clear (f : SubjectId → Nat) (s : SubjectId) : SubjectId → Nat :=
  fun t => if t = s then 0 else f t

def drop (f : SubjectId → Nat) (s : SubjectId) : SubjectId → Nat :=
  fun t => if t = s then f t - 1 else f t

/-- The server's alarm policy, run in ring 3 on each request it receives. -/
def policy (srv : Server) (client : SubjectId) (count : Nat) : Option Refusal :=
  if !InBound count then some .outOfBound
  else if srv.quota ≤ srv.outstanding client then some .quotaExceeded
  else none

def step (sys : System) : Op → System × Reply
  | .arm actor count =>
      if sys.auth.timerHolder ≠ some actor then (sys, .refused .noTimerCapability)
      else if !InBound count then (sys, .refused .outOfBound)
      else ({ sys with pit := { sys.pit with alarm := some count } }, .armed count)
  | .request client count =>
      if !sys.auth.reachesServer client then (sys, .refused .noEndpoint)
      else match policy sys.server client count with
        | some reason => (sys, .refused reason)
        | none =>
            ({ sys with server :=
                { sys.server with
                  outstanding := bump sys.server.outstanding client
                  queue := sys.server.queue ++ [(client, count)] } },
             .accepted client)
  | .collect actor =>
      if sys.auth.timerHolder ≠ some actor then (sys, .refused .notHolder)
      else if sys.expiries actor = 0 then (sys, .refused .nothingPending)
      else match sys.server.queue with
        | [] => ({ sys with expiries := clear sys.expiries actor }, .took 0)
        | (client, _) :: rest =>
            ({ sys with
                expiries := clear sys.expiries actor
                server := { sys.server with
                  outstanding := drop sys.server.outstanding client
                  queue := rest }
                wakes := bump sys.wakes client },
             .woke client)
  | .wait subject =>
      if sys.wakes subject = 0 then (sys, .refused .nothingPending)
      else ({ sys with wakes := clear sys.wakes subject }, .took (sys.wakes subject))
  | .expire =>
      match sys.pit.alarm, sys.auth.timerHolder with
      | some _, some holder =>
          ({ sys with
              pit := { sys.pit with alarm := none }
              expiries := bump sys.expiries holder },
           .delivered holder)
      | _, _ => (sys, .refused .notArmed)
  | .tick =>
      if sys.pit.preemption.isSome then ({ sys with ticks := sys.ticks + 1 }, .ticked)
      else (sys, .refused .notArmed)

/-! ## The timer capability -/

theorem arm_non_holder_unchanged (sys : System) (actor : SubjectId) (count : Nat)
    (h : sys.auth.timerHolder ≠ some actor) :
    step sys (.arm actor count) = (sys, .refused .noTimerCapability) := by
  simp [step, h]

theorem arm_out_of_bound_unchanged (sys : System) (actor : SubjectId) (count : Nat)
    (h : InBound count = false) :
    (step sys (.arm actor count)).1 = sys ∧
      (step sys (.arm actor count)).2 ≠ .armed count := by
  simp only [step]
  by_cases hh : sys.auth.timerHolder ≠ some actor <;> simp [hh, h]

theorem arm_accepted (sys : System) (actor : SubjectId) (count : Nat)
    (h : (step sys (.arm actor count)).2 = .armed count) :
    sys.auth.timerHolder = some actor ∧ InBound count = true ∧
      (step sys (.arm actor count)).1.pit =
        { preemption := sys.pit.preemption, alarm := some count } := by
  simp only [step] at h ⊢
  by_cases hh : sys.auth.timerHolder ≠ some actor
  · simp [hh] at h
  · by_cases hb : InBound count = false
    · simp [hh, hb] at h
    · simp only [Bool.not_eq_false] at hb
      simp_all

/-- The alarm is set only by an accepted arm from the timer-capability holder,
with a count in bound. -/
theorem alarm_set_only_by_holder (sys : System) (op : Op) (count : Nat)
    (h : (step sys op).1.pit.alarm = some count) :
    sys.pit.alarm = some count ∨
      ∃ actor, op = .arm actor count ∧ sys.auth.timerHolder = some actor ∧
        InBound count = true := by
  cases op with
  | arm actor n =>
      simp only [step] at h
      by_cases hh : sys.auth.timerHolder ≠ some actor
      · simp [hh] at h; exact Or.inl h
      · by_cases hb : InBound n = false
        · simp [hh, hb] at h; exact Or.inl h
        · simp only [Bool.not_eq_false] at hb
          simp [hh, hb] at h
          subst h
          exact Or.inr ⟨actor, rfl, by simpa using hh, hb⟩
  | request client n =>
      left; simp only [step] at h
      split at h
      · exact h
      · split at h <;> exact h
  | collect actor =>
      left; simp only [step] at h
      split at h
      · exact h
      · split at h
        · exact h
        · split at h <;> exact h
  | wait subject =>
      left; simp only [step] at h
      split at h <;> exact h
  | expire =>
      left; simp only [step] at h
      split at h
      · simp at h
      · exact h
  | tick =>
      left; simp only [step] at h
      split at h <;> exact h

/-! ## The kernel multiplexes the PIT -/

/-- No operation, the server's included, changes the kernel's preemption
deadline. -/
theorem preemption_unchanged (sys : System) (op : Op) :
    (step sys op).1.pit.preemption = sys.pit.preemption := by
  cases op <;> simp only [step]
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl

/-- Whatever alarm is armed, the programmed count is never later than the
kernel's preemption deadline. -/
theorem programmed_le_preemption (pit : Pit) (p : Nat) (h : pit.preemption = some p) :
    ∃ q, pit.programmed = some q ∧ q ≤ p := by
  unfold Pit.programmed
  rw [h]
  cases pit.alarm with
  | none => exact ⟨p, rfl, Nat.le_refl p⟩
  | some a => exact ⟨min p a, rfl, Nat.min_le_left p a⟩

/-- The preemption tick is accepted exactly when the kernel's deadline is
set, whatever the server armed. -/
theorem tick_independent_of_alarm (sys : System) (alarm : Option Nat) :
    (step { sys with pit := { sys.pit with alarm } } .tick).2 = (step sys .tick).2 := by
  simp only [step]
  split <;> rfl

/-- The preemption tick changes only the tick count. -/
theorem tick_footprint (sys : System) :
    (step sys .tick).1 = sys ∨ (step sys .tick).1 = { sys with ticks := sys.ticks + 1 } := by
  simp only [step]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## The kernel's expiry path -/

/-- The expiry interrupt touches only the alarm and the holder's expiry
notification: authority, preemption deadline, server state, wakes and ticks
are unchanged, and only the holder's expiry bits change. -/
theorem expire_footprint (sys : System) :
    let next := (step sys .expire).1
    next.auth = sys.auth ∧ next.pit.preemption = sys.pit.preemption ∧
      next.server.queue = sys.server.queue ∧
      next.server.outstanding = sys.server.outstanding ∧
      next.wakes = sys.wakes ∧ next.ticks = sys.ticks ∧
      (∀ s, sys.auth.timerHolder ≠ some s → next.expiries s = sys.expiries s) := by
  simp only
  simp only [step]
  split
  · rename_i holder _ hholder
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro s hs
    have : s ≠ holder := by intro e; subst e; exact hs hholder
    simp [bump, this]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- An expiry is delivered only to the timer-capability holder, and only
while an alarm is armed. -/
theorem expire_delivered_to_holder (sys : System) (holder : SubjectId)
    (h : (step sys .expire).2 = .delivered holder) :
    sys.auth.timerHolder = some holder ∧ sys.pit.alarm.isSome ∧
      (step sys .expire).1.pit.alarm = none := by
  simp only [step] at h ⊢
  split at h
  · rename_i _ _ hal hhold
    simp at h
    subst h
    simp [hal, hhold]
  · simp at h

/-- Only the holder ever has pending expiry bits. -/
def ExpiryBound (sys : System) : Prop :=
  ∀ s, sys.auth.timerHolder ≠ some s → sys.expiries s = 0

theorem step_preserves_auth (sys : System) (op : Op) : (step sys op).1.auth = sys.auth := by
  cases op <;> simp only [step]
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split <;> rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · split <;> rfl
  · split <;> rfl
  · split <;> rfl

theorem step_preserves_expiryBound (sys : System) (op : Op) (h : ExpiryBound sys) :
    ExpiryBound (step sys op).1 := by
  intro s hs
  rw [step_preserves_auth] at hs
  cases op with
  | expire => rw [(expire_footprint sys).2.2.2.2.2.2 s hs]; exact h s hs
  | collect actor =>
      simp only [step]
      split
      · exact h s hs
      · rename_i hholder
        have hholder : sys.auth.timerHolder = some actor := by simpa using hholder
        have hne : s ≠ actor := by intro e; subst e; exact hs hholder
        split
        · exact h s hs
        · split <;> simp [clear, hne, h s hs]
  | arm _ _ =>
      simp only [step]
      split
      · exact h s hs
      · split <;> exact h s hs
  | request _ _ =>
      simp only [step]
      split
      · exact h s hs
      · split <;> exact h s hs
  | wait _ => simp only [step]; split <;> exact h s hs
  | tick => simp only [step]; split <;> exact h s hs

/-- The holder's expiry bits are the only ones a step can raise, and no
other subject's ever change. -/
theorem expiry_only_to_holder (sys : System) (op : Op) (s : SubjectId)
    (hs : sys.auth.timerHolder ≠ some s) :
    (step sys op).1.expiries s = sys.expiries s := by
  cases op with
  | expire => exact (expire_footprint sys).2.2.2.2.2.2 s hs
  | collect actor =>
      simp only [step]
      split
      · rfl
      · rename_i hholder
        have hholder : sys.auth.timerHolder = some actor := by simpa using hholder
        have hne : s ≠ actor := by intro e; subst e; exact hs hholder
        split
        · rfl
        · split <;> simp [clear, hne]
  | arm _ _ =>
      simp only [step]
      split
      · rfl
      · split <;> rfl
  | request _ _ =>
      simp only [step]
      split
      · rfl
      · split <;> rfl
  | wait _ => simp only [step]; split <;> rfl
  | tick => simp only [step]; split <;> rfl

/-! ## Clients reach the server only through the endpoint -/

theorem request_without_endpoint_unchanged (sys : System) (client : SubjectId) (count : Nat)
    (h : sys.auth.reachesServer client = false) :
    step sys (.request client count) = (sys, .refused .noEndpoint) := by
  simp [step, h]

/-- A request outside the bound is refused without effect. -/
theorem request_out_of_bound_unchanged (sys : System) (client : SubjectId) (count : Nat)
    (h : InBound count = false) :
    (step sys (.request client count)).1 = sys ∧
      ((step sys (.request client count)).2 = .refused .noEndpoint ∨
        (step sys (.request client count)).2 = .refused .outOfBound) := by
  simp only [step]
  by_cases hr : sys.auth.reachesServer client = false
  · simp [hr]
  · simp only [Bool.not_eq_false] at hr
    simp [hr, policy, h]

/-- Every queued alarm belongs to a subject holding the server endpoint. -/
def QueueFromSenders (sys : System) : Prop :=
  ∀ entry ∈ sys.server.queue, sys.auth.reachesServer entry.1 = true

theorem step_preserves_queueFromSenders (sys : System) (op : Op) (h : QueueFromSenders sys) :
    QueueFromSenders (step sys op).1 := by
  intro entry hentry
  rw [step_preserves_auth]
  cases op with
  | request client count =>
      simp only [step] at hentry
      by_cases hr : sys.auth.reachesServer client = false
      · simp [hr] at hentry; exact h entry hentry
      · simp only [Bool.not_eq_false] at hr
        simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hentry
        split at hentry
        · exact h entry hentry
        · simp only [List.mem_append, List.mem_singleton] at hentry
          rcases hentry with hentry | hentry
          · exact h entry hentry
          · subst hentry; exact hr
  | collect actor =>
      simp only [step] at hentry
      split at hentry
      · exact h entry hentry
      · split at hentry
        · exact h entry hentry
        · split at hentry
          · exact h entry hentry
          · rename_i hq
            exact h entry (by rw [hq]; exact List.mem_cons_of_mem _ hentry)
  | arm _ _ =>
      simp only [step] at hentry
      split at hentry
      · exact h entry hentry
      · split at hentry <;> exact h entry hentry
  | wait _ => simp only [step] at hentry; split at hentry <;> exact h entry hentry
  | expire => simp only [step] at hentry; split at hentry <;> exact h entry hentry
  | tick => simp only [step] at hentry; split at hentry <;> exact h entry hentry

/-! ## Quotas -/

/-- No client has more outstanding alarms than the server's quota. -/
def WithinQuota (sys : System) : Prop :=
  ∀ client, sys.server.outstanding client ≤ sys.server.quota

theorem step_preserves_withinQuota (sys : System) (op : Op) (h : WithinQuota sys) :
    WithinQuota (step sys op).1 := by
  intro c
  cases op with
  | request client count =>
      simp only [step]
      by_cases hr : sys.auth.reachesServer client = false
      · simp [hr]; exact h c
      · simp only [Bool.not_eq_false] at hr
        simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · exact h c
        · rename_i hp
          unfold policy at hp
          by_cases hb : InBound count = false
          · simp [hb] at hp
          · simp only [Bool.not_eq_false] at hb
            simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
            by_cases hq : sys.server.quota ≤ sys.server.outstanding client
            · simp [hq] at hp
            · simp only [bump]
              by_cases hc : c = client
              · subst hc; simp; omega
              · simp [hc]; exact h c
  | collect actor =>
      simp only [step]
      split
      · exact h c
      · split
        · exact h c
        · split
          · exact h c
          · simp only [drop]
            split
            · exact Nat.le_trans (Nat.sub_le _ _) (h c)
            · exact h c
  | arm _ _ =>
      simp only [step]
      split
      · exact h c
      · split <;> exact h c
  | wait _ => simp only [step]; split <;> exact h c
  | expire => simp only [step]; split <;> exact h c
  | tick => simp only [step]; split <;> exact h c

/-- A request that would exceed the quota is refused without effect. -/
theorem request_over_quota_refused (sys : System) (client : SubjectId) (count : Nat)
    (hr : sys.auth.reachesServer client = true) (hb : InBound count = true)
    (hq : sys.server.quota ≤ sys.server.outstanding client) :
    step sys (.request client count) = (sys, .refused .quotaExceeded) := by
  simp [step, hr, policy, hb, hq]

/-! ## Wakes -/

/-- A client's wake bits rise only when the holder collects an expiry and
that client's alarm is at the head of the queue. -/
theorem wake_only_by_holder (sys : System) (op : Op) (client : SubjectId)
    (h : sys.wakes client < (step sys op).1.wakes client) :
    ∃ actor count rest, op = .collect actor ∧ sys.auth.timerHolder = some actor ∧
      sys.expiries actor ≠ 0 ∧ sys.server.queue = (client, count) :: rest := by
  cases op with
  | collect actor =>
      simp only [step] at h
      split at h
      · exact absurd h (Nat.lt_irrefl _)
      · rename_i hholder
        split at h
        · exact absurd h (Nat.lt_irrefl _)
        · rename_i hexp
          split at h
          · exact absurd h (Nat.lt_irrefl _)
          · rename_i head count rest hq
            simp only [bump] at h
            by_cases hc : client = head
            · subst hc
              exact ⟨actor, count, rest, rfl, by simpa using hholder, hexp, hq⟩
            · simp [hc] at h
  | wait subject =>
      simp only [step] at h
      split at h
      · exact absurd h (Nat.lt_irrefl _)
      · simp only [clear] at h
        split at h <;> omega
  | arm _ _ =>
      simp only [step] at h; split at h
      · exact absurd h (Nat.lt_irrefl _)
      · split at h <;> exact absurd h (Nat.lt_irrefl _)
  | request _ _ =>
      simp only [step] at h; split at h
      · exact absurd h (Nat.lt_irrefl _)
      · split at h <;> exact absurd h (Nat.lt_irrefl _)
  | expire => simp only [step] at h; split at h <;> exact absurd h (Nat.lt_irrefl _)
  | tick => simp only [step] at h; split at h <;> exact absurd h (Nat.lt_irrefl _)

/-! ## The boot system and its run

Subject A (1) is the client: it holds the send-only endpoint capability to
the server. B (2) holds nothing. C (3) is the timer server and the only
holder of the timer capability. The quota is one outstanding alarm per
client. The image has no preemption deadline of its own (`preemption :=
none`); the theorems above cover the multiplexed case. -/

def bootAuthority : Authority :=
  { timerHolder := some 3, reachesServer := fun s => s == 1 }

def bootSystem : System :=
  { auth := bootAuthority
    pit := { preemption := none, alarm := none }
    expiries := fun _ => 0
    server := { quota := 1, outstanding := fun _ => 0, queue := [] }
    wakes := fun _ => 0
    ticks := 0 }

theorem bootSystem_invariants :
    ExpiryBound bootSystem ∧ QueueFromSenders bootSystem ∧ WithinQuota bootSystem := by
  refine ⟨fun _ _ => rfl, fun _ h => by simp [bootSystem] at h, fun _ => by
    simp [bootSystem]⟩

def run (sys : System) : List Op → System × List Reply
  | [] => (sys, [])
  | op :: ops =>
      let (next, reply) := step sys op
      let (final, replies) := run next ops
      (final, reply :: replies)

/-- The boot run: B's arm and send are refused; A asks for an alarm with a
count outside the bound (refused by the server), then one in bound
(accepted); the server arms it; A's second request exceeds its quota; the
alarm expires and is delivered to C; C wakes A; A takes its wake bit. -/
def bootScript : List Op :=
  [.arm 2 1000, .request 2 1000,
   .request 1 65536, .request 1 65535, .arm 3 65535,
   .request 1 100,
   .expire, .collect 3, .wait 1]

theorem boot_run :
    (run bootSystem bootScript).2 =
      [.refused .noTimerCapability, .refused .noEndpoint,
       .refused .outOfBound, .accepted 1, .armed 65535,
       .refused .quotaExceeded,
       .delivered 3, .woke 1, .took 1] := by
  decide

/-! ## The allocation-free boot witness -/

def refusalCode : Refusal → UInt64
  | .noTimerCapability => 1
  | .outOfBound => 2
  | .noEndpoint => 3
  | .quotaExceeded => 4
  | .notHolder => 5
  | .nothingPending => 6
  | .notArmed => 7

/-- The kernel-checked answers: 1 accepted, `2 | reason << 8` refused, and
`4 | holder << 8` for an expiry delivered to the holder. -/
def kernelCode : Reply → UInt64
  | .armed _ => 1
  | .accepted _ => 1
  | .woke _ => 1
  | .took _ => 1
  | .ticked => 1
  | .refused reason => 2 + refusalCode reason * 0x100
  | .delivered holder => 4 + UInt64.ofNat holder * 0x100

/-- The kernel's part of a request: the endpoint check. The server's policy
runs afterwards in ring 3 and is not a kernel decision. -/
def kernelSend (sys : System) (client : SubjectId) : Reply :=
  if sys.auth.reachesServer client then .accepted client else .refused .noEndpoint

theorem kernelSend_refused_iff (sys : System) (client : SubjectId) (count : Nat) :
    kernelSend sys client = .refused .noEndpoint ↔
      step sys (.request client count) = (sys, .refused .noEndpoint) := by
  unfold kernelSend step
  by_cases hr : sys.auth.reachesServer client = false
  · simp [hr]
  · simp only [Bool.not_eq_false] at hr
    simp only [hr, ↓reduceIte, Bool.not_true, Bool.false_eq_true, reduceCtorEq, false_iff]
    split
    · rename_i reason hp
      have hne : reason ≠ .noEndpoint := by
        unfold policy at hp
        split at hp
        · simp at hp; subst hp; decide
        · split at hp
          · simp at hp; subst hp; decide
          · simp at hp
      simp [hne]
    · simp

/-- Allocation-free generated witness for the timer-server image's kernel
decisions on the boot authority.

* `event = 0`, an arm: `subject` asks for `word` counts. 1 when `subject` is
  the timer-capability holder C (3) and `1 ≤ word ≤ 65535`; otherwise
  `2 | 1 << 8` (no timer capability) or `2 | 2 << 8` (out of bound).
* `event = 1`, a send to the server's endpoint from `subject`: 1 for A (1),
  the only endpoint holder, and `2 | 3 << 8` (no endpoint) otherwise.
* `event = 2`, the PIT alarm interrupt; `word` is 1 when an alarm is armed:
  `4 | 3 << 8`, delivered to the holder, or `2 | 7 << 8` (not armed).
* `event = 3`, a wake: `subject` signals the wake notification of client
  `word`. 1 for the holder C waking A, `2 | 5 << 8` (not the holder)
  otherwise.
* Every other event is 0. -/
@[export leanos_timer_server_decide]
def timerServerDecide (event subject word : UInt64) : UInt64 :=
  if event == 0 then
    if subject != 3 then 0x102
    else if word == 0 || word > 65535 then 0x202
    else 1
  else if event == 1 then
    if subject == 1 then 1 else 0x302
  else if event == 2 then
    if word == 1 then 0x304 else 0x702
  else if event == 3 then
    if subject == 3 && word == 1 then 1 else 0x502
  else 0

/-- The system with A's alarm armed, after the accepted request. -/
def armedSystem : System :=
  (run bootSystem [.request 1 65535, .arm 3 65535]).1

/-- The witness gives the model's kernel answer on the boot system: arms
from each subject at and around the bound, sends from each subject, the
expiry with and without an armed alarm, and the holder's wake. -/
theorem timerServerDecide_agrees :
    timerServerDecide 0 3 65535 = kernelCode (step bootSystem (.arm 3 65535)).2 ∧
      timerServerDecide 0 3 1 = kernelCode (step bootSystem (.arm 3 1)).2 ∧
      timerServerDecide 0 3 0 = kernelCode (step bootSystem (.arm 3 0)).2 ∧
      timerServerDecide 0 3 65536 = kernelCode (step bootSystem (.arm 3 65536)).2 ∧
      timerServerDecide 0 1 1000 = kernelCode (step bootSystem (.arm 1 1000)).2 ∧
      timerServerDecide 0 2 1000 = kernelCode (step bootSystem (.arm 2 1000)).2 ∧
      timerServerDecide 1 1 0 = kernelCode (kernelSend bootSystem 1) ∧
      timerServerDecide 1 2 0 = kernelCode (kernelSend bootSystem 2) ∧
      timerServerDecide 1 3 0 = kernelCode (kernelSend bootSystem 3) ∧
      timerServerDecide 2 0 1 = kernelCode (step armedSystem .expire).2 ∧
      timerServerDecide 2 0 0 = kernelCode (step bootSystem .expire).2 ∧
      timerServerDecide 3 3 1 =
        kernelCode (step (step armedSystem .expire).1 (.collect 3)).2 ∧
      timerServerDecide 3 2 1 =
        kernelCode (step (step armedSystem .expire).1 (.collect 2)).2 := by
  decide

/-- The witness accepts an arm only from C and only in bound. -/
theorem timerServerDecide_arm_accepts (subject word : UInt64)
    (h : timerServerDecide 0 subject word = 1) :
    subject = 3 ∧ 1 ≤ word.toNat ∧ word.toNat ≤ maxCount := by
  unfold timerServerDecide at h
  simp only [beq_self_eq_true, ↓reduceIte] at h
  by_cases hs : subject = 3
  · subst hs
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hw : (word == 0 || decide (word > 65535)) = true
    · simp [hw] at h
    · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hw
      refine ⟨rfl, ?_, ?_⟩
      · have : word ≠ 0 := hw.1
        have h0 : word.toNat ≠ 0 := by
          intro e; apply this; exact UInt64.toNat_inj.mp (by simpa using e)
        omega
      · have : ¬ (65535 : UInt64) < word := hw.2
        rw [UInt64.lt_iff_toNat_lt] at this
        simp [maxCount] at this ⊢
        omega
  · have : (subject != 3) = true := by simpa using hs
    simp [this] at h

/-- The witness sends a send to the server only from A. -/
theorem timerServerDecide_send_accepts (subject word : UInt64)
    (h : timerServerDecide 1 subject word = 1) : subject = 1 := by
  unfold timerServerDecide at h
  by_cases hs : subject = 1
  · exact hs
  · simp [hs] at h

end LeanOS.TimerServer
