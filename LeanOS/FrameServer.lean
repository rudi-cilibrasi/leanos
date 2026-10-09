import LeanOS.FrameScrub
import LeanOS.FrameBudget

/-!
# Frame server subject behind a budget capability (issue #486)

Allocation policy moves out of the kernel into a ring-3 frame server.  The
kernel keeps the mechanism (who holds which pool frame, scrubbing, mapping)
and only *checks* the server's decisions.

* **The server's pool capability.**  The boot-fixed `System.server` holds one
  capability over the frames in `pool`, carrying the mapping rights
  `poolRights` (bit 0 read, bit 1 write).  No transition changes the server,
  the pool or the pool rights.
* **Budget capabilities.**  Each client holds a budget capability to the
  server: a limit `limit client` on the number of pool frames it may hold at
  once.  Only `revoke` changes a limit, and only to zero.
* **Decisions.**  The server answers a client's request with a `Decision`:
  grant a named pool frame with named rights, refuse with a typed reason
  (`budgetExhausted` or `poolExhausted`), reclaim one frame, or revoke the
  client's budget capability.  The server chooses the client, the frame, the
  rights and the reason; the kernel chooses nothing.
* **The kernel's check.**  `check` accepts a decision only from the server,
  and only if it is valid for the mechanism state: a granted frame is in the
  pool and free, the rights are a nonempty subset of the pool rights, and the
  client is below its limit; a refusal's reason is true; a reclaimed frame is
  held by that client.  An accepted decision has exactly the effect it names
  (`effect`); a rejected one changes nothing (`decide_rejected_unchanged`,
  `decide_accepted_effect`).
* **Scrub before publish.**  A grant scrubs the whole frame with
  `FrameScrub.scrubFrame` before the client can see it; reclaim and revoke
  leave the old bytes in place, exactly like `FrameScrub.release`.  So a
  released or revoked frame is scrubbed before it is reused, by whichever
  client (`grant_publishes_scrubbed`, `read_unwritten_zero`).

`Invariant` (pool without duplicates, every grant inside the pool with rights
inside the pool rights, every client within its limit, every unwritten held
frame zero) holds initially and is preserved by every step
(`step_preserves_invariant`).  `serverPolicy` is the honest policy the
`frame-server` image's ring-3 server implements; `serverPolicy_accepted`
shows the kernel's check never overrides it.

`frameServerCheck` is the allocation-free boot witness of `check`; the
`frame-server` image checks every decision of its ring-3 server against it,
and `frameServerCheck_agrees` proves it equals the model's encoded reply for
every system and decision.
-/
namespace LeanOS.FrameServer

open LeanOS
set_option linter.unusedSimpArgs false

abbrev SubjectId := Capability.SubjectId
abbrev FrameId := FrameAllocator.FrameId
abbrev ByteOffset := FrameScrub.ByteOffset

/-- Mapping-rights bits of a granted frame. -/
def readBit : UInt64 := 1
def writeBit : UInt64 := 2

/-- `requested` is a nonempty subset of `held`. -/
def rightsSubset (requested held : UInt64) : Bool :=
  requested != 0 && (requested &&& ~~~held) == 0

structure Grant where
  client : SubjectId
  rights : UInt64
  deriving DecidableEq, Repr

structure System where
  /-- The frame-server subject; holder of the pool capability. -/
  server : SubjectId
  /-- The frames the server's pool capability covers. -/
  pool : List FrameId
  /-- The mapping rights the pool capability carries. -/
  poolRights : UInt64
  /-- Each client's budget capability: how many pool frames it may hold. -/
  limit : SubjectId → Nat
  /-- The kernel's mechanism record: which client holds (has mapped) a frame. -/
  grant : FrameId → Option Grant
  bytes : FrameScrub.FrameBytes
  /-- False means the current holder has not written the frame. -/
  written : FrameId → Bool

def holds (sys : System) (client : SubjectId) (frame : FrameId) : Bool :=
  match sys.grant frame with
  | some g => g.client == client
  | none => false

/-- The number of pool frames a client holds. -/
def usage (sys : System) (client : SubjectId) : Nat :=
  sys.pool.countP fun frame => holds sys client frame

def hasFree (sys : System) : Bool :=
  sys.pool.any fun frame => (sys.grant frame).isNone

inductive Refusal where
  | budgetExhausted | poolExhausted
  deriving DecidableEq, Repr

inductive Decision where
  | grant (client : SubjectId) (frame : FrameId) (rights : UInt64)
  | refuse (client : SubjectId) (reason : Refusal)
  | reclaim (client : SubjectId) (frame : FrameId)
  | revoke (client : SubjectId)
  deriving DecidableEq, Repr

def Decision.client : Decision → SubjectId
  | .grant client _ _ | .refuse client _ | .reclaim client _ | .revoke client => client

inductive RejectReason where
  | notServer | outsidePool | frameInUse | rightsNotSubset | overBudget | notHolder
  | untruthfulRefusal
  deriving DecidableEq, Repr

inductive Reply where
  | granted (client : SubjectId) (frame : FrameId)
  | refused (client : SubjectId) (reason : Refusal)
  | reclaimed (client : SubjectId) (frame : FrameId)
  | revoked (client : SubjectId)
  | rejected (reason : RejectReason)
  deriving DecidableEq, Repr

/-- The kernel's whole role: is the server's decision valid for the
mechanism state?  `none` accepts it. -/
def check (sys : System) (caller : SubjectId) : Decision → Option RejectReason
  | .grant client frame rights =>
      if caller ≠ sys.server then some .notServer
      else if frame ∉ sys.pool then some .outsidePool
      else if (sys.grant frame).isSome then some .frameInUse
      else if !rightsSubset rights sys.poolRights then some .rightsNotSubset
      else if sys.limit client ≤ usage sys client then some .overBudget
      else none
  | .refuse client .budgetExhausted =>
      if caller ≠ sys.server then some .notServer
      else if usage sys client < sys.limit client then some .untruthfulRefusal
      else none
  | .refuse _ .poolExhausted =>
      if caller ≠ sys.server then some .notServer
      else if hasFree sys then some .untruthfulRefusal
      else none
  | .reclaim client frame =>
      if caller ≠ sys.server then some .notServer
      else if frame ∉ sys.pool then some .outsidePool
      else if !holds sys client frame then some .notHolder
      else none
  | .revoke _ =>
      if caller ≠ sys.server then some .notServer else none

def setGrant (grant : FrameId → Option Grant) (frame : FrameId) (value : Option Grant) :
    FrameId → Option Grant :=
  fun candidate => if candidate = frame then value else grant candidate

def setWritten (written : FrameId → Bool) (frame : FrameId) (value : Bool) :
    FrameId → Bool :=
  fun candidate => if candidate = frame then value else written candidate

/-- Exactly what a decision names: no frame, client or rights are chosen by
the kernel.  A grant scrubs the frame before publishing it; reclaim and revoke
retire the grant and leave the bytes. -/
def effect (sys : System) : Decision → System
  | .grant client frame rights =>
      { sys with grant := setGrant sys.grant frame (some { client, rights })
                 bytes := FrameScrub.scrubFrame sys.bytes frame
                 written := setWritten sys.written frame false }
  | .refuse _ _ => sys
  | .reclaim _ frame => { sys with grant := setGrant sys.grant frame none }
  | .revoke client =>
      { sys with limit := fun c => if c = client then 0 else sys.limit c
                 grant := fun frame => if holds sys client frame then none else sys.grant frame }

def replyOf : Decision → Reply
  | .grant client frame _ => .granted client frame
  | .refuse client reason => .refused client reason
  | .reclaim client frame => .reclaimed client frame
  | .revoke client => .revoked client

def decide (sys : System) (caller : SubjectId) (d : Decision) : System × Reply :=
  match check sys caller d with
  | some reason => (sys, .rejected reason)
  | none => (effect sys d, replyOf d)

/-- A client reads a byte of a frame it holds with the read right. -/
def read (sys : System) (client : SubjectId) (frame : FrameId) (offset : ByteOffset) :
    Option UInt8 :=
  match sys.grant frame with
  | some g =>
      if g.client = client ∧ (g.rights &&& readBit) ≠ 0 ∧ offset < FrameScrub.frameBytes then
        some (sys.bytes frame offset)
      else none
  | none => none

/-- A client writes a byte of a frame it holds with the write right. -/
def write (sys : System) (client : SubjectId) (frame : FrameId) (offset : ByteOffset)
    (value : UInt8) : Option System :=
  match sys.grant frame with
  | some g =>
      if g.client = client ∧ (g.rights &&& writeBit) ≠ 0 ∧ offset < FrameScrub.frameBytes then
        some { sys with bytes := FrameScrub.setByte sys.bytes frame offset value
                        written := setWritten sys.written frame true }
      else none
  | none => none

inductive Op where
  | decide (caller : SubjectId) (d : Decision)
  | write (client : SubjectId) (frame : FrameId) (offset : ByteOffset) (value : UInt8)

def step (sys : System) : Op → System
  | .decide caller d => (decide sys caller d).1
  | .write client frame offset value => (write sys client frame offset value).getD sys

/-! ## The kernel only checks -/

theorem decide_rejected_unchanged sys caller d reason
    (h : (decide sys caller d).2 = .rejected reason) : (decide sys caller d).1 = sys := by
  unfold decide at h ⊢
  split at h
  · rfl
  · cases d <;> simp [replyOf] at h

/-- An accepted decision passed the check and has exactly its named effect. -/
theorem decide_accepted_effect sys caller d
    (h : ∀ reason, (decide sys caller d).2 ≠ .rejected reason) :
    check sys caller d = none ∧ decide sys caller d = (effect sys d, replyOf d) := by
  unfold decide at h ⊢
  split
  · rename_i reason hr
    simp [hr] at h
  · rename_i hr
    exact ⟨hr, rfl⟩

/-- Every decision is either refused by the kernel without effect, or applied
exactly as the server named it. -/
theorem kernel_only_checks sys caller d :
    (∃ reason, check sys caller d = some reason ∧ decide sys caller d = (sys, .rejected reason)) ∨
      (check sys caller d = none ∧ decide sys caller d = (effect sys d, replyOf d)) := by
  unfold decide
  cases hc : check sys caller d with
  | some reason => exact Or.inl ⟨reason, rfl, rfl⟩
  | none => exact Or.inr ⟨rfl, rfl⟩

theorem check_server sys caller d (h : check sys caller d = none) : caller = sys.server := by
  by_cases hne : caller = sys.server
  · exact hne
  · cases d with
    | grant => simp [check, hne] at h
    | refuse _ reason => cases reason <;> simp [check, hne] at h
    | reclaim => simp [check, hne] at h
    | revoke => simp [check, hne] at h

/-- An accepted grant came from the server, names a free pool frame and rights
inside the pool rights for a client below its limit, and installs exactly
that grant, over a completely scrubbed frame. -/
theorem granted_exact sys caller client frame rights c f
    (h : (decide sys caller (.grant client frame rights)).2 = .granted c f) :
    c = client ∧ f = frame ∧ caller = sys.server ∧ frame ∈ sys.pool ∧
      sys.grant frame = none ∧ rightsSubset rights sys.poolRights = true ∧
      usage sys client < sys.limit client ∧
      let next := (decide sys caller (.grant client frame rights)).1
      next.grant frame = some { client, rights } ∧
      (∀ other, other ≠ frame → next.grant other = sys.grant other) ∧
      next.written frame = false ∧
      (∀ offset, offset < FrameScrub.frameBytes → next.bytes frame offset = FrameScrub.initialByte) := by
  unfold decide at h ⊢
  split at h
  · simp at h
  · rename_i hc
    simp only [replyOf, Reply.granted.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [check] at hc
    by_cases hs : caller = sys.server
    · by_cases hp : frame ∈ sys.pool
      · by_cases hg : (sys.grant frame).isSome = true
        · simp [hs, hp, hg] at hc
        · by_cases hr : rightsSubset rights sys.poolRights = true
          · by_cases hl : sys.limit client ≤ usage sys client
            · simp [hs, hp, hg, hr, hl] at hc
            · refine ⟨rfl, rfl, hs, hp, ?_, hr, by omega, ?_⟩
              · simpa using hg
              · simp only [effect, setGrant, setWritten, ite_true]
                refine ⟨trivial, ?_, trivial, ?_⟩
                · intro other hne; simp [hne]
                · intro offset hoffset; exact FrameScrub.scrubFrame_target _ _ _ hoffset
          · simp [hs, hp, hg, hr] at hc
      · simp [hs, hp] at hc
    · simp [hs] at hc

/-- A refusal transfers nothing, and its typed reason is true. -/
theorem refused_truthful sys caller client reason c r
    (h : (decide sys caller (.refuse client reason)).2 = .refused c r) :
    c = client ∧ r = reason ∧ (decide sys caller (.refuse client reason)).1 = sys ∧
      (reason = .budgetExhausted → sys.limit client ≤ usage sys client) ∧
      (reason = .poolExhausted → hasFree sys = false) := by
  unfold decide at h ⊢
  split at h
  · simp at h
  · rename_i hc
    simp only [replyOf, Reply.refused.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro hr; subst hr
      simp only [check] at hc
      by_cases hs : caller = sys.server
      · by_cases hu : usage sys client < sys.limit client
        · simp [hs, hu] at hc
        · omega
      · simp [hs] at hc
    · intro hr; subst hr
      simp only [check] at hc
      by_cases hs : caller = sys.server
      · cases hf : hasFree sys
        · rfl
        · simp [hs, hf] at hc
      · simp [hs] at hc

/-! ## The honest server policy is never overridden -/

def firstFree (sys : System) : Option FrameId :=
  sys.pool.find? fun frame => (sys.grant frame).isNone

/-- The policy of the `frame-server` image's ring-3 server: grant the first
free pool frame with the pool rights while the client is below its limit;
refuse with the true reason otherwise. -/
def serverPolicy (sys : System) (client : SubjectId) : Decision :=
  if usage sys client < sys.limit client then
    match firstFree sys with
    | some frame => .grant client frame sys.poolRights
    | none => .refuse client .poolExhausted
  else .refuse client .budgetExhausted

theorem serverPolicy_accepted sys client (hrights : sys.poolRights ≠ 0) :
    check sys sys.server (serverPolicy sys client) = none := by
  unfold serverPolicy
  by_cases hu : usage sys client < sys.limit client
  · simp only [hu, ite_true]
    cases hf : firstFree sys with
    | some frame =>
        have hmem := List.mem_of_find?_eq_some hf
        have hfree := List.find?_some hf
        have hpoolRights : rightsSubset sys.poolRights sys.poolRights = true := by
          simp [rightsSubset, hrights]
        simp [check, hmem, hpoolRights, Option.isNone_iff_eq_none.mp hfree]
        omega
    | none =>
        have hnone := List.find?_eq_none.mp hf
        have hfree : hasFree sys = false := by
          simp only [hasFree, List.any_eq_false]
          intro frame hmem
          simpa using hnone frame hmem
        simp [check, hfree]
  · simp only [hu, ite_false]
    simp [check, hu]

/-! ## Invariants: budgets, confinement, scrubbing -/

/-- Every grant is of a pool frame, with rights inside the pool rights. -/
def Confined (sys : System) : Prop :=
  ∀ frame g, sys.grant frame = some g →
    frame ∈ sys.pool ∧ rightsSubset g.rights sys.poolRights = true

def WithinBudget (sys : System) : Prop := ∀ client, usage sys client ≤ sys.limit client

/-- Every held frame its holder has not written contains only zero bytes:
nothing unscrubbed is ever visible to a client. -/
def ScrubInvariant (sys : System) : Prop :=
  ∀ frame g, sys.grant frame = some g → sys.written frame = false →
    ∀ offset, offset < FrameScrub.frameBytes → sys.bytes frame offset = FrameScrub.initialByte

def Invariant (sys : System) : Prop :=
  sys.pool.Nodup ∧ Confined sys ∧ WithinBudget sys ∧ ScrubInvariant sys

/-- Counting over a duplicate-free list after changing the predicate at one
member from false to `value`. -/
theorem countP_update {l : List FrameId} (hnodup : l.Nodup) {frame : FrameId}
    (hmem : frame ∈ l) {p q : FrameId → Bool} (hp : p frame = false)
    (hq : ∀ x, x ≠ frame → q x = p x) :
    l.countP q = l.countP p + (if q frame then 1 else 0) := by
  induction l with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.countP_cons]
      by_cases hhead : head = frame
      · subst hhead
        have htail : tail.countP q = tail.countP p := by
          apply List.countP_congr
          intro x hx
          have hne : x ≠ head := fun h => hnodup.1 (h ▸ hx)
          simp [hq x hne]
        rw [htail, hp]
        cases q head <;> simp
      · have hmem' : frame ∈ tail := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hhead
          · exact h
        rw [ih hnodup.2 hmem', hq head hhead]
        cases p head <;> cases q frame <;> simp <;> omega

theorem usage_grant (sys next : System) (hnodup : sys.pool.Nodup) (frame : FrameId)
    (hmem : frame ∈ sys.pool) (hfree : sys.grant frame = none)
    (client : SubjectId) (rights : UInt64) (c : SubjectId) (hpool : next.pool = sys.pool)
    (hgrant : next.grant = setGrant sys.grant frame (some { client, rights })) :
    usage next c = usage sys c + (if client = c then 1 else 0) := by
  unfold usage
  rw [hpool, countP_update hnodup hmem (p := fun f => holds sys c f)
    (q := fun f => holds next c f)]
  · simp [holds, hgrant, setGrant]
  · simp [holds, hfree]
  · intro x hne
    simp [holds, hgrant, setGrant, hne]

theorem usage_le_of_subset (sys next : System) (hpool : next.pool = sys.pool)
    (c : SubjectId) (h : ∀ frame, holds next c frame = true → holds sys c frame = true) :
    usage next c ≤ usage sys c := by
  unfold usage
  rw [hpool]
  exact List.countP_mono_left fun frame _ hx => h frame hx

theorem effect_revoke_grant (sys : System) client f :
    (effect sys (.revoke client)).grant f = if holds sys client f then none else sys.grant f :=
  rfl

theorem holds_revoke (sys : System) client c f :
    holds (effect sys (.revoke client)) c f = (!holds sys client f && holds sys c f) := by
  have hg := effect_revoke_grant sys client f
  by_cases hc : holds sys client f = true
  · rw [hc] at hg ⊢
    simp only [ite_true] at hg
    simp [holds, hg]
  · rw [Bool.not_eq_true] at hc
    rw [hc] at hg ⊢
    simp only [Bool.false_eq_true, ite_false] at hg
    simp only [Bool.not_false, Bool.true_and]
    unfold holds
    rw [hg]

theorem holds_reclaim (sys : System) client frame c f :
    holds (effect sys (.reclaim client frame)) c f = ((f != frame) && holds sys c f) := by
  by_cases hf : f = frame
  · subst hf; simp [holds, effect, setGrant]
  · simp [holds, effect, setGrant, hf]

theorem step_preserves_invariant sys op (hinv : Invariant sys) : Invariant (step sys op) := by
  obtain ⟨hnodup, hconf, hbudget, hscrub⟩ := hinv
  cases op with
  | decide caller d =>
      simp only [step]
      rcases kernel_only_checks sys caller d with ⟨reason, _, hdec⟩ | ⟨hc, hdec⟩
      · rw [hdec]; exact ⟨hnodup, hconf, hbudget, hscrub⟩
      · rw [hdec]
        simp only
        cases d with
        | grant client frame rights =>
            have hall := granted_exact sys caller client frame rights client frame
              (by simp [hdec, replyOf])
            obtain ⟨_, _, _, hp, hfree, hr, hu, -, -, -, -⟩ := hall
            refine ⟨hnodup, ?_, ?_, ?_⟩
            · intro f g hg
              simp only [effect, setGrant] at hg
              split at hg
              · rename_i hf; subst hf
                simp only [Option.some.injEq] at hg
                subst hg
                exact ⟨hp, hr⟩
              · exact hconf f g hg
            · intro c
              rw [usage_grant sys (effect sys (.grant client frame rights)) hnodup frame hp hfree
                client rights c rfl rfl]
              simp only [effect]
              have := hbudget c
              split
              · rename_i hcc; subst hcc; omega
              · omega
            · intro f g hg hw offset hoffset
              simp only [effect, setGrant, setWritten] at hg hw ⊢
              by_cases hf : f = frame
              · subst hf
                exact FrameScrub.scrubFrame_target _ _ _ hoffset
              · simp only [hf, ite_false] at hg hw
                rw [FrameScrub.scrubFrame_other _ _ _ _ hf]
                exact hscrub f g hg hw offset hoffset
        | refuse client reason => exact ⟨hnodup, hconf, hbudget, hscrub⟩
        | reclaim client frame =>
            refine ⟨hnodup, ?_, ?_, ?_⟩
            · intro f g hg
              simp only [effect, setGrant] at hg
              split at hg
              · simp at hg
              · exact hconf f g hg
            · intro c
              have hle : usage (effect sys (.reclaim client frame)) c ≤ usage sys c := by
                refine usage_le_of_subset sys (effect sys (.reclaim client frame)) rfl c ?_
                intro f hf
                rw [holds_reclaim] at hf
                simp only [Bool.and_eq_true] at hf
                exact hf.2
              have := hbudget c
              simp only [effect] at hle ⊢
              omega
            · intro f g hg hw offset hoffset
              simp only [effect, setGrant] at hg hw ⊢
              split at hg
              · simp at hg
              · exact hscrub f g hg hw offset hoffset
        | revoke client =>
            refine ⟨hnodup, ?_, ?_, ?_⟩
            · intro f g hg
              simp only [effect] at hg
              split at hg
              · simp at hg
              · exact hconf f g hg
            · intro c
              by_cases hcc : c = client
              · subst hcc
                have hzero : usage (effect sys (.revoke c)) c = 0 := by
                  unfold usage
                  rw [List.countP_eq_zero]
                  intro f _
                  simp [holds_revoke]
                simp only [effect] at hzero ⊢
                omega
              · have hle : usage (effect sys (.revoke client)) c ≤ usage sys c := by
                  refine usage_le_of_subset sys (effect sys (.revoke client)) rfl c ?_
                  intro f hf
                  rw [holds_revoke] at hf
                  simp only [Bool.and_eq_true] at hf
                  exact hf.2
                have := hbudget c
                simp only [effect, hcc, ite_false] at hle ⊢
                omega
            · intro f g hg hw offset hoffset
              simp only [effect] at hg hw ⊢
              split at hg
              · simp at hg
              · exact hscrub f g hg hw offset hoffset
  | write client frame offset value =>
      simp only [step]
      unfold write
      split
      · rename_i g hg
        split
        · rename_i hcond
          simp only [Option.getD_some]
          refine ⟨hnodup, hconf, hbudget, ?_⟩
          intro f g' hg' hw o ho
          simp only [setWritten] at hw ⊢
          by_cases hf : f = frame
          · subst hf; simp at hw
          · simp only [hf, ite_false] at hw
            simp only [FrameScrub.setByte, hf, false_and, ite_false]
            exact hscrub f g' hg' hw o ho
        · exact ⟨hnodup, hconf, hbudget, hscrub⟩
      · exact ⟨hnodup, hconf, hbudget, hscrub⟩

/-! ## The advertised results -/

/-- No client ever holds more pool frames than its budget capability allows,
whatever the server decides and whatever the clients write. -/
theorem budget_respected sys op (hinv : Invariant sys) client :
    usage (step sys op) client ≤ (step sys op).limit client :=
  (step_preserves_invariant sys op hinv).2.2.1 client

theorem decide_preserves_authority sys caller d :
    (decide sys caller d).1.server = sys.server ∧ (decide sys caller d).1.pool = sys.pool ∧
      (decide sys caller d).1.poolRights = sys.poolRights ∧
      ∀ client, (decide sys caller d).1.limit client ≤ sys.limit client := by
  rcases kernel_only_checks sys caller d with ⟨_, _, hdec⟩ | ⟨_, hdec⟩
  · rw [hdec]; exact ⟨rfl, rfl, rfl, fun _ => Nat.le_refl _⟩
  · rw [hdec]
    cases d with
    | grant => exact ⟨rfl, rfl, rfl, fun _ => Nat.le_refl _⟩
    | refuse => exact ⟨rfl, rfl, rfl, fun _ => Nat.le_refl _⟩
    | reclaim => exact ⟨rfl, rfl, rfl, fun _ => Nat.le_refl _⟩
    | revoke client =>
        refine ⟨rfl, rfl, rfl, fun c => ?_⟩
        simp only [effect]
        split <;> omega

/-- No amplification: no step changes the server, its pool or its rights, or
raises any budget; every grant stays inside the pool with rights inside the
pool rights. -/
theorem no_amplification sys op (hinv : Invariant sys) :
    (step sys op).server = sys.server ∧ (step sys op).pool = sys.pool ∧
      (step sys op).poolRights = sys.poolRights ∧
      (∀ client, (step sys op).limit client ≤ sys.limit client) ∧
      Confined (step sys op) := by
  refine ⟨?_, ?_, ?_, ?_, (step_preserves_invariant sys op hinv).2.1⟩
  all_goals cases op with
    | decide caller d =>
        have := decide_preserves_authority sys caller d
        simp only [step]
        first | exact this.1 | exact this.2.1 | exact this.2.2.1 | exact this.2.2.2
    | write client frame offset value =>
        simp only [step, write]
        split
        · split <;> simp
        · simp

/-- A grant publishes a completely scrubbed frame, whatever it held before
(a previous holder's data, or anything else): the new holder reads zero at
every offset. -/
theorem grant_publishes_scrubbed sys caller client frame rights
    (h : (decide sys caller (.grant client frame rights)).2 = .granted client frame)
    (hread : rights &&& readBit ≠ 0) offset (hoffset : offset < FrameScrub.frameBytes) :
    read (decide sys caller (.grant client frame rights)).1 client frame offset =
      some FrameScrub.initialByte := by
  obtain ⟨_, _, _, _, _, _, _, hgrant, _, _, hbytes⟩ := granted_exact sys caller client frame
    rights client frame h
  simp only [read, hgrant, true_and, hread, ne_eq, not_false_eq_true, hoffset, and_self,
    ite_true]
  rw [hbytes offset hoffset]

/-- Release (reclaim or revoke) does not scrub: it only retires the grant.
Scrubbing happens at the next publication (`grant_publishes_scrubbed`). -/
theorem release_preserves_bytes sys caller client frame :
    (decide sys caller (.reclaim client frame)).1.bytes = sys.bytes ∧
      (decide sys caller (.revoke client)).1.bytes = sys.bytes := by
  constructor <;> (unfold decide; split <;> rfl)

/-- Revocation retires every frame the client held and zeroes its budget. -/
theorem revoke_retires sys caller client
    (h : (decide sys caller (.revoke client)).2 = .revoked client) :
    (decide sys caller (.revoke client)).1.limit client = 0 ∧
      ∀ frame, holds (decide sys caller (.revoke client)).1 client frame = false := by
  unfold decide at h ⊢
  split at h
  · simp at h
  · refine ⟨by simp [effect], fun frame => ?_⟩
    simp [holds_revoke]

/-- In every invariant state, a client reading a frame it holds and has not
written reads zero: a released, reclaimed or revoked frame is scrubbed before
any client can see it again. -/
theorem read_unwritten_zero sys (hinv : Invariant sys) client frame offset g
    (hg : sys.grant frame = some g) (hw : sys.written frame = false)
    (hoffset : offset < FrameScrub.frameBytes) (value : UInt8)
    (hread : read sys client frame offset = some value) :
    value = FrameScrub.initialByte := by
  simp only [read, hg] at hread
  split at hread
  · simp only [Option.some.injEq] at hread
    rw [← hread]
    exact hinv.2.2.2 frame g hg hw offset hoffset
  · simp at hread

/-! ## The boot witness -/

def opWord : Decision → UInt64
  | .grant .. => 1
  | .refuse _ .budgetExhausted => 2
  | .refuse _ .poolExhausted => 3
  | .reclaim .. => 4
  | .revoke _ => 5

/-- What the kernel tells the witness about the named frame: 0 outside the
pool, 1 free, 2 held by the named client, 3 held by another client.  For a
pool-exhausted refusal it is 1 when some pool frame is free and 0 otherwise. -/
def frameView (sys : System) (client : SubjectId) (frame : FrameId) : UInt64 :=
  if frame ∉ sys.pool then 0
  else match sys.grant frame with
    | none => 1
    | some g => if g.client = client then 2 else 3

def decisionView (sys : System) : Decision → UInt64
  | .grant client frame _ | .reclaim client frame => frameView sys client frame
  | .refuse _ .poolExhausted => if hasFree sys then 1 else 0
  | _ => 0

def requestedWord : Decision → UInt64
  | .grant _ _ rights => rights
  | _ => 0

def RejectReason.code : RejectReason → UInt64
  | .notServer => 1 | .outsidePool => 2 | .frameInUse => 3 | .rightsNotSubset => 4
  | .overBudget => 5 | .notHolder => 6 | .untruthfulRefusal => 7

/-- Reply words: what the kernel hands back.  `budgetExhaustedCode` and
`poolExhaustedCode` are the client's typed rejections; `0xf00 + reason` is the
kernel refusing the server's decision. -/
def grantedCode : UInt64 := 1
def reclaimedCode : UInt64 := 3
def revokedCode : UInt64 := 5
def budgetExhaustedCode : UInt64 := 0x100
def poolExhaustedCode : UInt64 := 0x200

def encodeReply : Reply → UInt64
  | .granted .. => grantedCode
  | .refused _ .budgetExhausted => budgetExhaustedCode
  | .refused _ .poolExhausted => poolExhaustedCode
  | .reclaimed .. => reclaimedCode
  | .revoked _ => revokedCode
  | .rejected reason => 0xf00 + reason.code

/-- Allocation-free boot witness of `check` for a decision of the server.
`op` is `opWord`, `view` is `decisionView`, `usage` and `limit` are the named
client's, `requested` the granted rights and `held` the pool rights.  The
answer is `encodeReply` of the kernel's reply; an unknown op is 0xf08. -/
@[export leanos_frame_server_check]
def frameServerCheck (op view usage limit requested held : UInt64) : UInt64 :=
  if op == 1 then
    if view == 0 then 0xf02
    else if view != 1 then 0xf03
    else if !(requested != 0 && (requested &&& ~~~held) == 0) then 0xf04
    else if limit ≤ usage then 0xf05
    else 1
  else if op == 2 then
    if usage < limit then 0xf07 else 0x100
  else if op == 3 then
    if view != 0 then 0xf07 else 0x200
  else if op == 4 then
    if view == 0 then 0xf02 else if view == 2 then 3 else 0xf06
  else if op == 5 then 5
  else 0xf08

theorem ofNat_le_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a ≤ UInt64.ofNat b) ↔ a ≤ b := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb]

theorem ofNat_lt_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (UInt64.ofNat a < UInt64.ofNat b) ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb]

/-- The witness is the model's check: for every system and every decision of
the server (with the named client's usage and limit below 2^64), the witness
over the kernel's words answers exactly the encoded reply of `decide`. -/
theorem grant_cases (sys : System) (frame : FrameId) :
    (∃ g, sys.grant frame = some g) ∨ sys.grant frame = none := by
  cases sys.grant frame <;> simp

theorem frameServerCheck_agrees (sys : System) (d : Decision)
    (husage : usage sys d.client < 2 ^ 64) (hlimit : sys.limit d.client < 2 ^ 64) :
    frameServerCheck (opWord d) (decisionView sys d) (UInt64.ofNat (usage sys d.client))
        (UInt64.ofNat (sys.limit d.client)) (requestedWord d) sys.poolRights =
      encodeReply (decide sys sys.server d).2 := by
  have hle := ofNat_le_iff hlimit husage
  have hlt := ofNat_lt_iff husage hlimit
  cases d with
  | grant client frame rights =>
      simp only [Decision.client] at hle hlt
      show frameServerCheck 1 (frameView sys client frame) (UInt64.ofNat (usage sys client))
          (UInt64.ofNat (sys.limit client)) rights sys.poolRights = _
      by_cases hp : frame ∈ sys.pool
      · rcases grant_cases sys frame with ⟨g, hg⟩ | hg
        · have hc : check sys sys.server (.grant client frame rights) = some .frameInUse := by
            simp [check, hp, hg]
          simp only [decide, hc]
          by_cases hcl : g.client = client
          · have hv : frameView sys client frame = 2 := by simp [frameView, hp, hg, hcl]
            rw [hv]; rfl
          · have hv : frameView sys client frame = 3 := by simp [frameView, hp, hg, hcl]
            rw [hv]; rfl
        · have hv : frameView sys client frame = 1 := by simp [frameView, hp, hg]
          rw [hv]
          by_cases hr : rightsSubset rights sys.poolRights = true
          · have hr' : (rights != 0 && (rights &&& ~~~sys.poolRights) == 0) = true := hr
            by_cases hl : sys.limit client ≤ usage sys client
            · have hc : check sys sys.server (.grant client frame rights) = some .overBudget := by
                simp [check, hp, hg, hr, hl]
              simp only [decide, hc]
              simp [frameServerCheck, hr', hle.mpr hl, encodeReply, RejectReason.code]
            · have hc : check sys sys.server (.grant client frame rights) = none := by
                simp [check, hp, hg, hr, hl]
              have hl' : ¬ (UInt64.ofNat (sys.limit client) ≤ UInt64.ofNat (usage sys client)) :=
                fun h => hl (hle.mp h)
              simp only [decide, hc]
              simp [frameServerCheck, hr', hl', encodeReply, replyOf, grantedCode]
          · have hr' : (rights != 0 && (rights &&& ~~~sys.poolRights) == 0) = false := by
              simpa [rightsSubset] using hr
            have hc : check sys sys.server (.grant client frame rights) = some .rightsNotSubset := by
              simp [check, hp, hg, hr]
            simp only [decide, hc]
            simp only [frameServerCheck, hr']
            rfl
      · have hv : frameView sys client frame = 0 := by simp [frameView, hp]
        have hc : check sys sys.server (.grant client frame rights) = some .outsidePool := by
          simp [check, hp]
        rw [hv]; simp only [decide, hc]; rfl
  | refuse client reason =>
      simp only [Decision.client] at hle hlt
      cases reason with
      | budgetExhausted =>
          show frameServerCheck 2 0 (UInt64.ofNat (usage sys client))
              (UInt64.ofNat (sys.limit client)) 0 sys.poolRights = _
          by_cases hu : usage sys client < sys.limit client
          · have hc : check sys sys.server (.refuse client .budgetExhausted) =
                some .untruthfulRefusal := by simp [check, hu]
            simp only [decide, hc]
            simp [frameServerCheck, hlt.mpr hu, encodeReply, RejectReason.code]
          · have hc : check sys sys.server (.refuse client .budgetExhausted) = none := by
              simp [check, hu]
            have hu' : ¬ (UInt64.ofNat (usage sys client) < UInt64.ofNat (sys.limit client)) :=
              fun h => hu (hlt.mp h)
            simp only [decide, hc]
            simp [frameServerCheck, hu', encodeReply, replyOf, budgetExhaustedCode]
      | poolExhausted =>
          show frameServerCheck 3 (if hasFree sys then 1 else 0) (UInt64.ofNat (usage sys client))
              (UInt64.ofNat (sys.limit client)) 0 sys.poolRights = _
          cases hf : hasFree sys
          · have hc : check sys sys.server (.refuse client .poolExhausted) = none := by
              simp [check, hf]
            simp only [decide, hc]; rfl
          · have hc : check sys sys.server (.refuse client .poolExhausted) =
                some .untruthfulRefusal := by simp [check, hf]
            simp only [decide, hc]; rfl
  | reclaim client frame =>
      show frameServerCheck 4 (frameView sys client frame) _ _ 0 sys.poolRights = _
      by_cases hp : frame ∈ sys.pool
      · rcases grant_cases sys frame with ⟨g, hg⟩ | hg
        · by_cases hcl : g.client = client
          · have hv : frameView sys client frame = 2 := by simp [frameView, hp, hg, hcl]
            have hc : check sys sys.server (.reclaim client frame) = none := by
              simp [check, hp, hg, hcl, holds]
            rw [hv]; simp only [decide, hc]; rfl
          · have hv : frameView sys client frame = 3 := by simp [frameView, hp, hg, hcl]
            have hc : check sys sys.server (.reclaim client frame) = some .notHolder := by
              simp [check, hp, hg, hcl, holds]
            rw [hv]; simp only [decide, hc]; rfl
        · have hv : frameView sys client frame = 1 := by simp [frameView, hp, hg]
          have hc : check sys sys.server (.reclaim client frame) = some .notHolder := by
            simp [check, hp, hg, holds]
          rw [hv]; simp only [decide, hc]; rfl
      · have hv : frameView sys client frame = 0 := by simp [frameView, hp]
        have hc : check sys sys.server (.reclaim client frame) = some .outsidePool := by
          simp [check, hp]
        rw [hv]; simp only [decide, hc]; rfl
  | revoke client =>
      have hc : check sys sys.server (.revoke client) = none := by simp [check]
      show frameServerCheck 5 0 _ _ 0 sys.poolRights = _
      simp only [decide, hc]; rfl

/-- A decision from anyone but the server is refused without effect; the
boot image accepts the decision syscall only from the server subject. -/
theorem decide_not_server sys caller d (h : caller ≠ sys.server) :
    decide sys caller d = (sys, .rejected .notServer) := by
  cases d with
  | grant => simp [decide, check, h]
  | refuse _ reason => cases reason <;> simp [decide, check, h]
  | reclaim => simp [decide, check, h]
  | revoke => simp [decide, check, h]

/-! ## The `frame-server` image's run in the model

Subject C (3) is the server, with a two-frame pool (frames 0 and 1) and read
and write rights.  Client A (1) holds a budget capability of one frame, client
B (2) one of two.  Every pool frame starts with arbitrary residue (0xff). -/

def bootSystem : System :=
  { server := 3, pool := [0, 1], poolRights := readBit ||| writeBit
    limit := fun client => if client = 1 then 1 else if client = 2 then 2 else 0
    grant := fun _ => none
    bytes := fun _ _ => 0xff
    written := fun _ => false }

def lastOffset : ByteOffset := FrameScrub.frameBytes - 1

/-- A's request: the policy grants pool frame 0. -/
def grantedA : System := (decide bootSystem 3 (serverPolicy bootSystem 1)).1
/-- A writes its canary 0xa5 to the first and last byte. -/
def writtenA : System :=
  ((write grantedA 1 0 0 0xa5).bind fun s => write s 1 0 lastOffset 0xa5).getD grantedA
/-- The server revokes A's budget capability: frame 0 is free, its bytes are
A's. -/
def revokedA : System := (decide writtenA 3 (.revoke 1)).1
/-- B's request: the policy grants the same frame 0, scrubbed. -/
def grantedB : System := (decide revokedA 3 (serverPolicy revokedA 2)).1

theorem boot_grant_a :
    serverPolicy bootSystem 1 = .grant 1 0 3 ∧
      (decide bootSystem 3 (serverPolicy bootSystem 1)).2 = .granted 1 0 ∧
      frameServerCheck 1 1 0 1 3 3 = grantedCode := by
  decide

theorem boot_written_a :
    read writtenA 1 0 0 = some 0xa5 ∧ read writtenA 1 0 lastOffset = some 0xa5 := by
  decide

/-- A's second request is over its budget: the policy refuses it with the
typed `budgetExhausted`, the kernel accepts the refusal, and nothing changes,
although frame 1 is still free. -/
theorem boot_refuse_a :
    serverPolicy writtenA 1 = .refuse 1 .budgetExhausted ∧
      (decide writtenA 3 (serverPolicy writtenA 1)).2 = .refused 1 .budgetExhausted ∧
      hasFree writtenA = true ∧
      frameServerCheck 2 0 1 1 0 3 = budgetExhaustedCode := by
  decide

/-- Revocation: A holds nothing and has no budget; frame 0 still holds A's
canary (release does not scrub). -/
theorem boot_revoke_a :
    (decide writtenA 3 (.revoke 1)).2 = .revoked 1 ∧ usage revokedA 1 = 0 ∧
      revokedA.limit 1 = 0 ∧ revokedA.grant 0 = none ∧
      revokedA.bytes 0 0 = 0xa5 ∧ revokedA.bytes 0 lastOffset = 0xa5 ∧
      frameServerCheck 5 0 1 1 0 3 = revokedCode := by
  decide

/-- B, with a larger budget, proceeds: it is granted the same frame 0, and
reads zero where A's canary was. -/
theorem boot_grant_b :
    serverPolicy revokedA 2 = .grant 2 0 3 ∧
      (decide revokedA 3 (serverPolicy revokedA 2)).2 = .granted 2 0 ∧
      read grantedB 2 0 0 = some 0 ∧ read grantedB 2 0 lastOffset = some 0 ∧
      read grantedB 1 0 0 = none ∧
      frameServerCheck 1 1 0 2 3 3 = grantedCode := by
  decide

/-- The hostile decisions the image's kernel checks at boot are all refused
by the witness: a frame outside the pool, a frame in use, rights outside the
pool rights, an over-budget grant, an untruthful budget refusal, a reclaim of
a frame the client does not hold, and an unknown op. -/
theorem boot_hostile_refused :
    frameServerCheck 1 0 0 1 3 3 = 0xf02 ∧ frameServerCheck 1 3 0 1 3 3 = 0xf03 ∧
      frameServerCheck 1 1 0 1 4 3 = 0xf04 ∧ frameServerCheck 1 1 0 1 0 3 = 0xf04 ∧
      frameServerCheck 1 1 1 1 3 3 = 0xf05 ∧ frameServerCheck 2 0 0 1 0 3 = 0xf07 ∧
      frameServerCheck 4 3 0 1 0 3 = 0xf06 ∧ frameServerCheck 0 1 0 1 3 3 = 0xf08 := by
  decide

end LeanOS.FrameServer
