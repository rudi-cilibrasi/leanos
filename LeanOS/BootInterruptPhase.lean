import LeanOS.InterruptEntry

/-!
# Finite boot-interrupt phase contract

This module models who owns interrupt dispatch between the Multiboot2 handoff
and the published runtime IDT.  The phases are the reviewed publication chain
`inherited → bootstrap32 → bootstrap64 → runtime`, plus the absorbing
`terminal` latch.  Every phase names its permitted table, descriptor width,
stack assumption, and terminal target.  Before the runtime manifest exists, an
admitted event may only record a bounded boot-phase reason and stop: it never
returns, never selects a subject, never arms return authority, and never
advances the publication chain.  Real descriptor loads, x86 delivery, the
one-instruction long-mode IDTR handoff window, assembly stubs, and the final
binary remain trusted/tested boundaries rather than theorem claims.
-/
namespace LeanOS.BootInterruptPhase

open LeanOS
set_option linter.unusedSimpArgs false

inductive Phase where
  | inherited | bootstrap32 | bootstrap64 | runtime | terminal
  deriving DecidableEq, Repr

/-- Position along the reviewed publication chain.  `terminal` outranks every
publication so monotonicity covers the fail-closed latch. -/
def Phase.rank : Phase → Nat
  | .inherited => 0 | .bootstrap32 => 1 | .bootstrap64 => 2
  | .runtime => 3 | .terminal => 4

inductive TableId where
  | firmware | bootstrap32 | bootstrap64 | runtime
  deriving DecidableEq, Repr

inductive GateWidth where
  | legacy8 | long16
  deriving DecidableEq, Repr

inductive StackAssumption where
  | firmwareOwned | bootStack32 | bootStack64 | runtimeManifest
  deriving DecidableEq, Repr

inductive TerminalTarget where
  | firmwareUnknown | bootstrapStub32 | bootstrapStub64 | runtimeVector2Gate
  deriving DecidableEq, Repr

/-- Per-phase descriptor policy.  `runtimeReturnAuthority` records whether an
accepted event in that phase may ever lead to an authorized CPL3 return. -/
structure PhaseContract where
  table : TableId
  width : GateWidth
  stack : StackAssumption
  vector2Owned : Bool
  terminalTarget : TerminalTarget
  runtimeReturnAuthority : Bool
  deriving DecidableEq, Repr

/-- The absorbing `terminal` phase executes nothing and has no contract. -/
def contract? : Phase → Option PhaseContract
  | .inherited =>
      some ⟨.firmware, .legacy8, .firmwareOwned, false, .firmwareUnknown, false⟩
  | .bootstrap32 =>
      some ⟨.bootstrap32, .legacy8, .bootStack32, true, .bootstrapStub32, false⟩
  | .bootstrap64 =>
      some ⟨.bootstrap64, .long16, .bootStack64, true, .bootstrapStub64, false⟩
  | .runtime =>
      some ⟨.runtime, .long16, .runtimeManifest, true, .runtimeVector2Gate, true⟩
  | .terminal => none

/-- Every kernel-owned phase owns vector 2; only the runtime phase may ever
authorize a return, and no legacy 8-byte gate survives into a long-mode phase. -/
theorem contract_table :
    (∀ phase contract, contract? phase = some contract →
      (contract.vector2Owned = false ↔ phase = .inherited) ∧
      (contract.runtimeReturnAuthority = true ↔ phase = .runtime) ∧
      (contract.width = .legacy8 ↔ (phase = .inherited ∨ phase = .bootstrap32))) ∧
    contract? .terminal = none := by
  refine ⟨?_, rfl⟩
  intro phase contract hcontract
  cases phase <;> simp [contract?] at hcontract <;> subst hcontract <;> decide

inductive EarlyReason where
  | earlyEvent
  | unownedInheritedWindow
  | wrongPublication (requested : TableId)
  | missingRuntimePrerequisite
  deriving DecidableEq, Repr

/-- The bounded diagnostic recorded by an early terminal latch. -/
structure EarlyHaltRecord where
  phase : Phase
  vector : UInt64
  hasErrorCode : Bool
  fromUser : Bool
  reason : EarlyReason
  deriving DecidableEq, Repr

/-- Boot-interrupt ownership state.  `business` is the not-yet-published
business state (page tables, PCI control, allocations, model replay); the type
is abstract precisely so no early transition can depend on or change it. -/
structure State (α : Type) where
  phase : Phase
  latched : Option EarlyHaltRecord := none
  returnAuthorityArmed : Bool := false
  business : α

structure RuntimePrerequisites where
  tssLoaded : Bool
  istStacksInitialized : Bool
  gatesMatchRuntimeManifest : Bool
  deriving DecidableEq, Repr

inductive TableLoad where
  | publishBootstrap32
  | publishBootstrap64
  | publishRuntime (prerequisites : RuntimePrerequisites)
  deriving DecidableEq, Repr

def TableLoad.table : TableLoad → TableId
  | .publishBootstrap32 => .bootstrap32
  | .publishBootstrap64 => .bootstrap64
  | .publishRuntime _ => .runtime

/-- A hardware event observed before, during, or after the bootstrap window.
Only the finite descriptor-relevant shape is modeled; saved registers are
deliberately absent. -/
structure EarlyEvent where
  vector : UInt64
  hasErrorCode : Bool
  fromUser : Bool
  deriving DecidableEq, Repr

inductive Outcome where
  | published (next : Phase)
  | terminalLatched (record : EarlyHaltRecord)
  | alreadyTerminal (record : EarlyHaltRecord)
  | runtimeDelegated (vector : UInt64)
  deriving DecidableEq, Repr

structure StepResult (α : Type) where
  state : State α
  outcome : Outcome

private def latch (state : State α) (record : EarlyHaltRecord) : StepResult α :=
  { state := { state with
      phase := .terminal
      latched := some record
      returnAuthorityArmed := false }
    outcome := .terminalLatched record }

private def publicationRecord (phase : Phase) (reason : EarlyReason) : EarlyHaltRecord :=
  ⟨phase, 0, false, false, reason⟩

/-- Publish one table.  Only the exact next chain step is accepted; the runtime
manifest additionally requires its TSS/IST/manifest prerequisites.  Every wrong
publication fails closed into the absorbing terminal latch. -/
def publish (state : State α) (load : TableLoad) : StepResult α :=
  match state.latched with
  | some record => { state, outcome := .alreadyTerminal record }
  | none =>
      match state.phase, load with
      | .inherited, .publishBootstrap32 =>
          { state := { state with phase := .bootstrap32 }
            outcome := .published .bootstrap32 }
      | .bootstrap32, .publishBootstrap64 =>
          { state := { state with phase := .bootstrap64 }
            outcome := .published .bootstrap64 }
      | .bootstrap64, .publishRuntime prerequisites =>
          if prerequisites.tssLoaded && prerequisites.istStacksInitialized &&
              prerequisites.gatesMatchRuntimeManifest then
            { state := { state with phase := .runtime }
              outcome := .published .runtime }
          else
            latch state (publicationRecord state.phase .missingRuntimePrerequisite)
      | phase, load =>
          latch state (publicationRecord phase (.wrongPublication load.table))

/-- Dispatch one event under the current ownership phase.  Runtime events are
delegated unchanged to the separate ordinary/terminal runtime contracts; the
inherited window is typed as unowned; every bootstrap event is terminal. -/
def dispatch (state : State α) (event : EarlyEvent) : StepResult α :=
  match state.latched with
  | some record => { state, outcome := .alreadyTerminal record }
  | none =>
      match state.phase with
      | .runtime => { state, outcome := .runtimeDelegated event.vector }
      | .inherited =>
          latch state
            ⟨.inherited, event.vector, event.hasErrorCode, event.fromUser,
              .unownedInheritedWindow⟩
      | phase =>
          latch state
            ⟨phase, event.vector, event.hasErrorCode, event.fromUser, .earlyEvent⟩

inductive Operation where
  | load (table : TableLoad)
  | event (event : EarlyEvent)

def step (state : State α) : Operation → StepResult α
  | .load table => publish state table
  | .event event => dispatch state event

def run (state : State α) : List Operation → State α
  | [] => state
  | operation :: rest => run (step state operation).state rest

theorem step_total (state : State α) operation :
    ∃ result, step state operation = result := ⟨_, rfl⟩

theorem step_deterministic (state : State α) operation first second
    (hfirst : step state operation = first) (hsecond : step state operation = second) :
    first = second := by rw [hfirst] at hsecond; exact hsecond

theorem publish_preserves_business (state : State α) load :
    (publish state load).state.business = state.business := by
  unfold publish
  split
  · rfl
  · split <;> first | rfl | (split <;> rfl)

theorem dispatch_preserves_business (state : State α) event :
    (dispatch state event).state.business = state.business := by
  unfold dispatch
  split
  · rfl
  · split <;> rfl

/-- No boot-interrupt transition reads or writes the business state. -/
theorem step_preserves_business (state : State α) operation :
    (step state operation).state.business = state.business := by
  cases operation with
  | load table => exact publish_preserves_business state table
  | event event => exact dispatch_preserves_business state event

/-- No boot-interrupt transition can arm runtime return authority. -/
theorem step_never_arms_return_authority (state : State α) operation
    (hunarmed : state.returnAuthorityArmed = false) :
    (step state operation).state.returnAuthorityArmed = false := by
  cases operation with
  | load table =>
      show (publish state table).state.returnAuthorityArmed = false
      unfold publish
      split
      · exact hunarmed
      · split <;> first | exact hunarmed | rfl | (split <;> first | exact hunarmed | rfl)
  | event event =>
      show (dispatch state event).state.returnAuthorityArmed = false
      unfold dispatch
      split
      · exact hunarmed
      · split <;> first | exact hunarmed | rfl

/-- Every admitted bootstrap-phase event is one immediate absorbing terminal
latch carrying the bounded reason; nothing else changes. -/
theorem owned_bootstrap_event_terminal (state : State α) event
    (hphase : state.phase = .bootstrap32 ∨ state.phase = .bootstrap64)
    (hlatched : state.latched = none) :
    let record : EarlyHaltRecord :=
      ⟨state.phase, event.vector, event.hasErrorCode, event.fromUser, .earlyEvent⟩
    dispatch state event =
      { state := { state with
          phase := .terminal
          latched := some record
          returnAuthorityArmed := false }
        outcome := .terminalLatched record } := by
  rcases hphase with hphase | hphase <;> simp [dispatch, hlatched, hphase, latch]

/-- An event never advances the publication chain: the phase either stays or
enters the absorbing terminal latch. -/
theorem dispatch_never_advances_publication (state : State α) event :
    (dispatch state event).state.phase = state.phase ∨
      (dispatch state event).state.phase = .terminal := by
  unfold dispatch
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl

/-- An event never yields an ordinary-handler delegation before the runtime
manifest is published. -/
theorem early_event_never_delegated (state : State α) event vector
    (hphase : state.phase ≠ .runtime) :
    (dispatch state event).outcome ≠ .runtimeDelegated vector := by
  cases hlatched : state.latched with
  | some record => simp [dispatch, hlatched]
  | none =>
      cases hphase' : state.phase with
      | runtime => exact absurd hphase' hphase
      | inherited => simp [dispatch, hlatched, hphase', latch]
      | bootstrap32 => simp [dispatch, hlatched, hphase', latch]
      | bootstrap64 => simp [dispatch, hlatched, hphase', latch]
      | terminal => simp [dispatch, hlatched, hphase', latch]

private theorem Phase.rank_le_four (phase : Phase) : phase.rank ≤ 4 := by
  cases phase <;> decide

/-- Publication is monotonic along the reviewed chain; nothing moves backward
and nothing reloads the inherited table. -/
theorem publish_monotonic (state : State α) load :
    state.phase.rank ≤ (publish state load).state.phase.rank := by
  unfold publish
  split
  · exact Nat.le_refl _
  · split
    · simp_all [Phase.rank]
    · simp_all [Phase.rank]
    · split
      · simp_all [Phase.rank]
      · simp_all [latch, Phase.rank]
    · simpa [latch, Phase.rank] using Phase.rank_le_four state.phase

/-- No step ever produces the inherited phase from a kernel-owned phase. -/
theorem inherited_unreachable (state : State α) operation
    (howned : state.phase ≠ .inherited) :
    (step state operation).state.phase ≠ .inherited := by
  cases operation with
  | load table =>
      show (publish state table).state.phase ≠ .inherited
      unfold publish
      split
      · exact howned
      · split
        · simp
        · simp
        · split <;> simp [latch]
        · simp [latch]
  | event event =>
      show (dispatch state event).state.phase ≠ .inherited
      unfold dispatch
      split
      · exact howned
      · split
        · exact howned
        · simp [latch]
        · simp [latch]

/-- An accepted publication is exactly one forward chain step. -/
theorem published_is_exact_successor (state : State α) load next
    (hpublished : (publish state load).outcome = .published next) :
    (state.phase = .inherited ∧ next = .bootstrap32 ∧ load = .publishBootstrap32) ∨
    (state.phase = .bootstrap32 ∧ next = .bootstrap64 ∧ load = .publishBootstrap64) ∨
    (state.phase = .bootstrap64 ∧ next = .runtime ∧
      ∃ prerequisites, load = .publishRuntime prerequisites ∧
        prerequisites.tssLoaded = true ∧
        prerequisites.istStacksInitialized = true ∧
        prerequisites.gatesMatchRuntimeManifest = true) := by
  cases hlatched : state.latched with
  | some record => simp [publish, hlatched] at hpublished
  | none =>
      cases hphase : state.phase with
      | inherited =>
          cases load with
          | publishBootstrap32 =>
              simp [publish, hlatched, hphase] at hpublished
              exact Or.inl ⟨rfl, hpublished.symm, rfl⟩
          | publishBootstrap64 => simp [publish, hlatched, hphase, latch] at hpublished
          | publishRuntime prerequisites =>
              simp [publish, hlatched, hphase, latch] at hpublished
      | bootstrap32 =>
          cases load with
          | publishBootstrap32 => simp [publish, hlatched, hphase, latch] at hpublished
          | publishBootstrap64 =>
              simp [publish, hlatched, hphase] at hpublished
              exact Or.inr (Or.inl ⟨rfl, hpublished.symm, rfl⟩)
          | publishRuntime prerequisites =>
              simp [publish, hlatched, hphase, latch] at hpublished
      | bootstrap64 =>
          cases load with
          | publishBootstrap32 => simp [publish, hlatched, hphase, latch] at hpublished
          | publishBootstrap64 => simp [publish, hlatched, hphase, latch] at hpublished
          | publishRuntime prerequisites =>
              by_cases hprereq : (prerequisites.tssLoaded &&
                  prerequisites.istStacksInitialized &&
                  prerequisites.gatesMatchRuntimeManifest) = true
              · simp [publish, hlatched, hphase, hprereq] at hpublished
                have hbits := hprereq
                simp [Bool.and_eq_true] at hbits
                exact Or.inr (Or.inr ⟨rfl, hpublished.symm,
                  prerequisites, rfl, hbits.1.1, hbits.1.2, hbits.2⟩)
              · simp [publish, hlatched, hphase, hprereq, latch] at hpublished
      | runtime =>
          cases load <;> simp [publish, hlatched, hphase, latch] at hpublished
      | terminal =>
          cases load <;> simp [publish, hlatched, hphase, latch] at hpublished

/-- The runtime manifest cannot be published before its TSS, IST stacks, and
reviewed gate manifest exist. -/
theorem runtime_requires_prerequisites (state : State α) prerequisites
    (hpublished : (publish state (.publishRuntime prerequisites)).outcome =
      .published .runtime) :
    state.phase = .bootstrap64 ∧ state.latched = none ∧
      prerequisites.tssLoaded = true ∧
      prerequisites.istStacksInitialized = true ∧
      prerequisites.gatesMatchRuntimeManifest = true := by
  have := published_is_exact_successor state (.publishRuntime prerequisites) .runtime hpublished
  rcases this with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨hphase, _, ⟨actual, hload, htss, hist, hgates⟩⟩
  · cases h
  · cases h
  · cases hload
    refine ⟨hphase, ?_, htss, hist, hgates⟩
    cases hlatched : state.latched with
    | none => rfl
    | some record => simp [publish, hlatched] at hpublished

/-- Runtime events are delegated unchanged: this model neither replaces nor
weakens the separate runtime vector-2 terminal contract. -/
theorem runtime_defers_to_runtime_contract (state : State α) event
    (hphase : state.phase = .runtime) (hlatched : state.latched = none) :
    dispatch state event = { state, outcome := .runtimeDelegated event.vector } := by
  simp [dispatch, hlatched, hphase]

/-- The runtime vector-2 target named by the phase table is the unchanged
reviewed terminal NMI contract, still absent from the ordinary manifest. -/
theorem runtime_vector2_contract_unchanged :
    (contract? .runtime).map (·.terminalTarget) = some .runtimeVector2Gate ∧
    InterruptEntry.validateTerminalManifest InterruptEntry.terminalManifest = true ∧
    InterruptEntry.nmiEntry ∉ InterruptEntry.manifest := by
  exact ⟨rfl, InterruptEntry.reviewed_terminal_manifest_valid, InterruptEntry.nmi_not_ordinary⟩

/-- Once latched, every operation is absorbed with the original record. -/
theorem terminal_absorbing (state : State α) record operation
    (hlatched : state.latched = some record) :
    step state operation = { state, outcome := .alreadyTerminal record } := by
  cases operation with
  | load table => simp [step, publish, hlatched]
  | event event => simp [step, dispatch, hlatched]

/-- Absorption extends to every finite operation suffix. -/
theorem terminal_suffix_absorbing (state : State α) record operations
    (hlatched : state.latched = some record) :
    run state operations = state := by
  induction operations generalizing state with
  | nil => rfl
  | cons operation rest ih =>
      simp only [run, terminal_absorbing state record operation hlatched]
      exact ih state hlatched

/-- A latched early event also absorbs every suffix while preserving the exact
business state and leaving return authority unarmed. -/
theorem owned_bootstrap_event_terminal_absorbing (state : State α) event operations
    (hphase : state.phase = .bootstrap32 ∨ state.phase = .bootstrap64)
    (hlatched : state.latched = none) :
    let record : EarlyHaltRecord :=
      ⟨state.phase, event.vector, event.hasErrorCode, event.fromUser, .earlyEvent⟩
    let next := (dispatch state event).state
    (dispatch state event).outcome = .terminalLatched record ∧
      next.phase = .terminal ∧
      next.latched = some record ∧
      next.returnAuthorityArmed = false ∧
      next.business = state.business ∧
      run next operations = next := by
  have hterminal := owned_bootstrap_event_terminal state event hphase hlatched
  refine ⟨by rw [hterminal], by rw [hterminal], by rw [hterminal], by rw [hterminal],
    by rw [hterminal], ?_⟩
  exact terminal_suffix_absorbing _ _ operations (by rw [hterminal])

/-- The orderly reviewed publication sequence reaches the runtime phase without
any latch and without touching business state or return authority. -/
theorem orderly_publication_witness (business : α) :
    run { phase := .inherited, business }
      [.load .publishBootstrap32, .load .publishBootstrap64,
        .load (.publishRuntime ⟨true, true, true⟩)] =
      { phase := .runtime, latched := none, returnAuthorityArmed := false, business } := by
  rfl

/-- Concrete non-vacuity witnesses: a vector-2 event and an error-code fault
latch the absorbing terminal record in both bootstrap phases. -/
theorem bootstrap_event_witnesses :
    let base : State UInt64 := { phase := .inherited, business := 0x5a }
    let published32 := (publish base .publishBootstrap32).state
    let published64 := (publish published32 .publishBootstrap64).state
    let nmi : EarlyEvent := ⟨2, false, false⟩
    let fault : EarlyEvent := ⟨13, true, false⟩
    (dispatch published32 nmi).outcome =
        .terminalLatched ⟨.bootstrap32, 2, false, false, .earlyEvent⟩ ∧
      (dispatch published64 fault).outcome =
        .terminalLatched ⟨.bootstrap64, 13, true, false, .earlyEvent⟩ ∧
      (dispatch published64 fault).state.business = 0x5a := by
  native_decide

/-! ## Fixed-width corpus boundary

The scalar expectation below is the version-one encoding replayed through the
generated allocation-free `InterruptEntry.bootPhaseDemo` adapter, hosted C, and
the boot image.  Word 4 carries an opaque business token so the boundary also
witnesses business-state preservation. -/

def EarlyReason.code : EarlyReason → UInt64
  | .earlyEvent => 0
  | .unownedInheritedWindow => 1
  | .wrongPublication .firmware => 2
  | .wrongPublication .bootstrap32 => 3
  | .wrongPublication .bootstrap64 => 4
  | .wrongPublication .runtime => 5
  | .missingRuntimePrerequisite => 6

private def phaseOfCode : UInt64 → Option Phase
  | 0 => some .inherited
  | 1 => some .bootstrap32
  | 2 => some .bootstrap64
  | 3 => some .runtime
  | 4 => some .terminal
  | _ => none

/-- Canonical prior latch used by the corpus rows that model repeated events
and attempted progress after an early terminal record. -/
def canonicalLatchRecord : EarlyHaltRecord :=
  ⟨.bootstrap32, 2, false, false, .earlyEvent⟩

private def encodeOutcome (result : StepResult UInt64) : UInt64 :=
  let businessByte := result.state.business % 256
  match result.outcome with
  | .published next => 1 + UInt64.ofNat next.rank * 0x100 + businessByte * 0x10000
  | .terminalLatched record =>
      2 + UInt64.ofNat record.phase.rank * 0x100 + businessByte * 0x10000 +
        record.vector % 256 * 0x1000000 +
        (if record.hasErrorCode then 0x100000000 else 0) +
        (if record.fromUser then 0x200000000 else 0) +
        record.reason.code * 0x400000000
  | .alreadyTerminal _ => 3 + businessByte * 0x10000
  | .runtimeDelegated vector => 4 + businessByte * 0x10000 + vector % 256 * 0x1000000

/-- Rich-model expectation for the bounded generated-C boot-phase classifier.
The five scalar words encode the phase, one operation, its detail word, the
prior latch selector, and an opaque business token. -/
def bootPhaseModelExpected (phase operation detail latchWord business : UInt64) : UInt64 :=
  match phaseOfCode phase with
  | none => 0x8000000000000021
  | some decodedPhase =>
      if operation = 0 || operation > 4 then 0x8000000000000022
      else if latchWord > 1 then 0x8000000000000023
      else
        let state : State UInt64 :=
          { phase := decodedPhase
            latched := if latchWord = 1 then some canonicalLatchRecord else none
            business }
        if operation = 1 then encodeOutcome (publish state .publishBootstrap32)
        else if operation = 2 then encodeOutcome (publish state .publishBootstrap64)
        else if operation = 3 then
          encodeOutcome (publish state (.publishRuntime
            ⟨detail % 2 = 1, detail / 2 % 2 = 1, detail / 4 % 2 = 1⟩))
        else
          encodeOutcome (dispatch state
            ⟨detail % 256, detail / 256 % 2 = 1, detail / 512 % 2 = 1⟩)

theorem bootPhaseModelExpected_total phase operation detail latchWord business :
    ∃ result, bootPhaseModelExpected phase operation detail latchWord business = result :=
  ⟨_, rfl⟩

end LeanOS.BootInterruptPhase
