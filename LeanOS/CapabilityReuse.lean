import LeanOS.EndpointIPC

/-!
# Generation-checked capability reuse

This executable scenario fixes one endpoint slot, revokes the capability stored
there, and installs a different endpoint in the same slot.  The old userspace
word is rejected without changing state; the freshly encoded word authorizes a
send to the replacement endpoint.
-/
namespace LeanOS.CapabilityReuse

open LeanOS

private def subjects : Capability.SubjectId → Bool := fun subject => subject < 2

private def bootstrapCapability : Capability.Capability :=
  { object := 7, kind := .memory, rights := Capability.allRights }

private def initialCapabilities : Capability.State :=
  { subjects
    objects := fun object => object = 7
    kinds := fun object => if object = 7 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 9 then some bootstrapCapability else none }

private def initial : EndpointIPC.State :=
  { capabilities := initialCapabilities
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    issued := fun _ => false
    sendHistory := fun _ => [] }

private def root := (EndpointIPC.create initial 10 0 0).state
private def sendOnly : Capability.Rights := { send := true }
private def withSender := (EndpointIPC.delegate root 0 0 1 0 sendOnly).1

def rootHandle : CapabilityHandle.Handle := { slot := 0, identity := 1 }
def staleHandle : CapabilityHandle.Handle := { slot := 0, identity := 2 }

private def revoked :=
  (EndpointIPC.revokeHandle withSender 0 rootHandle 1 staleHandle).1

def reusedState : EndpointIPC.State := (EndpointIPC.create revoked 11 1 0).state
def currentHandle : CapabilityHandle.Handle := { slot := 0, identity := 3 }
def payload : EndpointIPC.Payload := { word0 := 0xCAFE, word1 := 0xBEEF }

private def wrongKindState : EndpointIPC.State :=
  { reusedState with
    capabilities :=
      { reusedState.capabilities with
        slots := fun subject slot =>
          if subject = 1 ∧ slot = 0 then
            some ⟨7, .memory, Capability.allRights, 4, none⟩
          else reusedState.capabilities.slots subject slot } }

private def exhaustedState : EndpointIPC.State :=
  { initial with
    capabilities :=
      { initialCapabilities with nextIdentity := CapabilityHandle.generationReserved } }

def staleWord : UInt64 := (CapabilityHandle.encode staleHandle).getD 0
def currentWord : UInt64 := (CapabilityHandle.encode currentHandle).getD 0

/-- Userspace-facing adapter: decode the canonical word, then use the shared
generation-aware endpoint consumer in trusted caller context. -/
def sendWord (state : EndpointIPC.State) (caller : Capability.SubjectId)
    (word : UInt64) (message : EndpointIPC.Payload) : EndpointIPC.Outcome EndpointIPC.SendError :=
  match CapabilityHandle.decode word with
  | .error _ => EndpointIPC.reject state .staleHandle
  | .ok handle => EndpointIPC.sendHandle state caller handle message

/-! ## Fixed-width differential-oracle adapter -/

private def encodeOutcome (outcome : EndpointIPC.Outcome EndpointIPC.SendError)
    (message : EndpointIPC.Payload) : UInt64 :=
  let accepted := match outcome.result with
    | .accepted => 1
    | .rejected _ => 0
  let original := if outcome.state.mailbox 10 =
      some { endpoint := 10, sender := 1, payload := message } then 2 else 0
  let replacement := if outcome.state.mailbox 11 =
      some { endpoint := 11, sender := 1, payload := message } then 4 else 0
  let replacementEmpty := if outcome.state.mailbox 11 = none then 8 else 0
  accepted + original + replacement + replacementEmpty

def encodeScenarioEvent (event nextState evidence : UInt64)
    (handle : CapabilityHandle.Handle) (endpoint : Capability.ObjectId) : UInt64 :=
  event + nextState * 0x100 + evidence * 0x10000 +
    UInt64.ofNat handle.slot * 0x1000000 +
    UInt64.ofNat handle.identity * 0x10000000000 +
    UInt64.ofNat endpoint * 0x100000000000000

private def initialTransition (caller word word0 word1 : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else
    match CapabilityHandle.decode word with
    | .error _ => 0
    | .ok handle =>
      match CapabilityHandle.resolve withSender.capabilities caller.toNat handle .endpoint with
      | .error _ => 0
      | .ok capability =>
        let message := { word0, word1 }
        let outcome := EndpointIPC.sendHandle withSender caller.toNat handle message
        match outcome.result with
        | .rejected _ => 0
        | .accepted =>
          encodeScenarioEvent 1 1 (encodeOutcome outcome message) handle capability.object

private def replacementEvidence (cleared installed : EndpointIPC.State) : UInt64 :=
  let clearedSlot := if cleared.capabilities.slots 1 0 = none then 1 else 0
  let installedSlot := if (installed.capabilities.slots 1 0).isSome then 2 else 0
  let replacementLive := if installed.capabilities.objects 11 &&
      installed.capabilities.kinds 11 = some .endpoint then 4 else 0
  let mailboxEmpty := if installed.mailbox 11 = none then 8 else 0
  clearedSlot + installedSlot + replacementLive + mailboxEmpty

private def replacementTransition (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else
    match CapabilityHandle.decode word with
    | .error _ => 0
    | .ok target =>
      let cleared := EndpointIPC.revokeHandle withSender 0 rootHandle caller.toNat target
      match cleared.2 with
      | .rejected _ => 0
      | .accepted =>
        let installed := EndpointIPC.create cleared.1 11 caller.toNat target.slot
        match installed.result with
        | .rejected _ => 0
        | .accepted =>
          match installed.state.capabilities.slots caller.toNat target.slot with
          | none => 0
          | some capability =>
            let fresh := CapabilityHandle.issue target.slot capability
            encodeScenarioEvent 2 2 (replacementEvidence cleared.1 installed.state)
              fresh capability.object

private def staleReplayTransition (caller word word0 word1 : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else
    match CapabilityHandle.decode word with
    | .error _ => 0
    | .ok handle =>
      let message := { word0, word1 }
      let outcome := EndpointIPC.sendHandle reusedState caller.toNat handle message
      match outcome.result with
      | .accepted => 0
      | .rejected .staleHandle =>
        match reusedState.capabilities.slots caller.toNat handle.slot with
        | none => 0
        | some capability =>
          encodeScenarioEvent 3 3 (encodeOutcome outcome message) handle capability.object
      | .rejected _ => 0

private def freshSendTransition (caller word word0 word1 : UInt64) : UInt64 :=
  if caller != 1 || word != currentWord then 0
  else
    match CapabilityHandle.decode word with
    | .error _ => 0
    | .ok handle =>
      match CapabilityHandle.resolve reusedState.capabilities caller.toNat handle .endpoint with
      | .error _ => 0
      | .ok capability =>
        let message := { word0, word1 }
        let outcome := EndpointIPC.sendHandle reusedState caller.toNat handle message
        match outcome.result with
        | .rejected _ => 0
        | .accepted =>
          encodeScenarioEvent 4 4 (encodeOutcome outcome message) handle capability.object

private def wrongKindTransition (caller word word0 word1 : UInt64) : UInt64 :=
  if caller != 1 || word != 4 * 65536 then 0
  else
    match CapabilityHandle.decode word with
    | .error _ => 0
    | .ok handle =>
      let outcome := EndpointIPC.sendHandle wrongKindState caller.toNat handle { word0, word1 }
      match outcome.result with
      | .rejected .staleHandle =>
        encodeScenarioEvent 5 0 (encodeOutcome outcome payload) handle 7
      | _ => 0

private def exhaustedTransition (caller : UInt64) : UInt64 :=
  if caller != 1 then 0
  else
    let outcome := EndpointIPC.create exhaustedState 12 caller.toNat 1
    match outcome.result with
    | .rejected .generationExhausted =>
      encodeScenarioEvent 6 0 1 { slot := 1, identity := 0 } 12
    | _ => 0

/-- Executable reference construction for the scenario's canonical states. -/
def authoritativeScenarioTransition (state caller word word0 word1 : UInt64) : UInt64 :=
  if state = 0 then initialTransition caller word word0 word1
  else if state = 1 then replacementTransition caller word
  else if state = 2 then staleReplayTransition caller word word0 word1
  else if state = 3 then freshSendTransition caller word word0 word1
  else if state = 4 then wrongKindTransition caller word word0 word1
  else if state = 6 then exhaustedTransition caller
  else 0

private def encodeScenarioScalar (event nextState evidence slot generation endpoint : UInt64) :
    UInt64 :=
  event + nextState * 0x100 + evidence * 0x10000 + slot * 0x1000000 +
    generation * 0x10000000000 + endpoint * 0x100000000000000

/-- Allocation-free whole-scenario transition used at the freestanding ABI.
The all-input refinement theorem below connects this executable form to the
canonical decoder and shared capability/endpoint operations. -/
private def initialScalar (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else encodeScenarioScalar 1 1 11 0 2 10

private def replacementScalar (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else encodeScenarioScalar 2 2 15 0 3 11

private def staleReplayScalar (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != staleWord then 0
  else encodeScenarioScalar 3 3 8 0 2 11

private def freshSendScalar (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != currentWord then 0
  else encodeScenarioScalar 4 4 5 0 3 11

private def wrongKindScalar (caller word : UInt64) : UInt64 :=
  if caller != 1 || word != 4 * 65536 then 0
  else encodeScenarioScalar 5 0 8 0 4 7

private def exhaustedScalar (caller : UInt64) : UInt64 :=
  if caller != 1 then 0 else encodeScenarioScalar 6 0 1 1 0 12

def scenarioTransition (state caller word _word0 _word1 : UInt64) : UInt64 :=
  if state = 0 then initialScalar caller word
  else if state = 1 then replacementScalar caller word
  else if state = 2 then staleReplayScalar caller word
  else if state = 3 then freshSendScalar caller word
  else if state = 4 then wrongKindScalar caller word
  else if state = 6 then exhaustedScalar caller
  else 0

def modelExpected (state caller word word0 word1 : UInt64) : UInt64 :=
  authoritativeScenarioTransition state caller word word0 word1

/-- Generated whole-scenario adapter. Each call executes the allocation-free
form proved equivalent to the authoritative transition over its scalar ABI. -/
@[export leanos_capability_reuse_demo]
def capabilityReuseDemo (state caller word word0 word1 : UInt64) : UInt64 :=
  scenarioTransition state caller word word0 word1

def AdmittedState (state : UInt64) : Prop :=
  state = 0 ∨ state = 1 ∨ state = 2 ∨ state = 3 ∨ state = 4 ∨ state = 6

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem initialTransition_value (word0 word1 : UInt64) :
    initialTransition 1 staleWord word0 word1 = encodeScenarioScalar 1 1 11 0 2 10 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem replacementTransition_value :
    replacementTransition 1 staleWord = encodeScenarioScalar 2 2 15 0 3 11 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem staleReplayTransition_value (word0 word1 : UInt64) :
    staleReplayTransition 1 staleWord word0 word1 = encodeScenarioScalar 3 3 8 0 2 11 := by
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem freshSendTransition_value (word0 word1 : UInt64) :
    freshSendTransition 1 currentWord word0 word1 = encodeScenarioScalar 4 4 5 0 3 11 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem wrongKindTransition_value (word0 word1 : UInt64) :
    wrongKindTransition 1 (4 * 65536) word0 word1 = encodeScenarioScalar 5 0 8 0 4 7 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem exhaustedTransition_value :
    exhaustedTransition 1 = encodeScenarioScalar 6 0 1 1 0 12 := by
  native_decide

private theorem initialScalar_refines (caller word word0 word1 : UInt64) :
    initialScalar caller word = initialTransition caller word word0 word1 := by
  by_cases hcaller : caller = 1
  · subst caller
    by_cases hword : word = staleWord
    · subst word
      exact (initialTransition_value word0 word1).symm
    · simp [initialScalar, initialTransition, hword]
  · simp [initialScalar, initialTransition, hcaller]

private theorem replacementScalar_refines (caller word : UInt64) :
    replacementScalar caller word = replacementTransition caller word := by
  by_cases hcaller : caller = 1
  · subst caller
    by_cases hword : word = staleWord
    · subst word
      exact replacementTransition_value.symm
    · simp [replacementScalar, replacementTransition, hword]
  · simp [replacementScalar, replacementTransition, hcaller]

private theorem staleReplayScalar_refines (caller word word0 word1 : UInt64) :
    staleReplayScalar caller word = staleReplayTransition caller word word0 word1 := by
  by_cases hcaller : caller = 1
  · subst caller
    by_cases hword : word = staleWord
    · subst word
      exact (staleReplayTransition_value word0 word1).symm
    · simp [staleReplayScalar, staleReplayTransition, hword]
  · simp [staleReplayScalar, staleReplayTransition, hcaller]

private theorem freshSendScalar_refines (caller word word0 word1 : UInt64) :
    freshSendScalar caller word = freshSendTransition caller word word0 word1 := by
  by_cases hcaller : caller = 1
  · subst caller
    by_cases hword : word = currentWord
    · subst word
      exact (freshSendTransition_value word0 word1).symm
    · simp [freshSendScalar, freshSendTransition, hword]
  · simp [freshSendScalar, freshSendTransition, hcaller]

private theorem wrongKindScalar_refines (caller word word0 word1 : UInt64) :
    wrongKindScalar caller word = wrongKindTransition caller word word0 word1 := by
  by_cases hcaller : caller = 1
  · subst caller
    by_cases hword : word = (262144 : UInt64)
    · subst word
      exact (wrongKindTransition_value word0 word1).symm
    · simp [wrongKindScalar, wrongKindTransition, hword]
  · simp [wrongKindScalar, wrongKindTransition, hcaller]

private theorem exhaustedScalar_refines (caller : UInt64) :
    exhaustedScalar caller = exhaustedTransition caller := by
  by_cases hcaller : caller = 1
  · subst caller
    exact exhaustedTransition_value.symm
  · simp [exhaustedScalar, exhaustedTransition, hcaller]

/-- The allocation-free scalar transition agrees with the canonical decoder,
capability resolver, and endpoint operations for every word, caller, payload,
and state. States outside the bounded protocol reject in both definitions. -/
theorem scenarioTransition_refines_authoritative_all_inputs
    (state caller word word0 word1 : UInt64) :
    scenarioTransition state caller word word0 word1 =
      authoritativeScenarioTransition state caller word word0 word1 := by
  by_cases h0 : state = 0
  · subst state
    simpa [scenarioTransition, authoritativeScenarioTransition] using
      initialScalar_refines caller word word0 word1
  · by_cases h1 : state = 1
    · subst state
      simpa [scenarioTransition, authoritativeScenarioTransition] using
        replacementScalar_refines caller word
    · by_cases h2 : state = 2
      · subst state
        simpa [scenarioTransition, authoritativeScenarioTransition] using
          staleReplayScalar_refines caller word word0 word1
      · by_cases h3 : state = 3
        · subst state
          simpa [scenarioTransition, authoritativeScenarioTransition] using
            freshSendScalar_refines caller word word0 word1
        · by_cases h4 : state = 4
          · subst state
            simpa [scenarioTransition, authoritativeScenarioTransition] using
              wrongKindScalar_refines caller word word0 word1
          · by_cases h6 : state = 6
            · subst state
              simpa [scenarioTransition, authoritativeScenarioTransition] using
                exhaustedScalar_refines caller
            · simp [scenarioTransition, authoritativeScenarioTransition, h0, h1, h2, h3,
                h4, h6]

theorem exported_adapter_refines_authoritative_all_inputs
    (state caller word word0 word1 : UInt64) :
    capabilityReuseDemo state caller word word0 word1 =
      authoritativeScenarioTransition state caller word word0 word1 := by
  exact scenarioTransition_refines_authoritative_all_inputs state caller word word0 word1

theorem exported_adapter_refines_authoritative_all_admitted_inputs
    (state caller word word0 word1 : UInt64) (_hadmitted : AdmittedState state) :
    capabilityReuseDemo state caller word word0 word1 =
      authoritativeScenarioTransition state caller word word0 word1 := by
  exact exported_adapter_refines_authoritative_all_inputs state caller word word0 word1

theorem exported_adapter_refines_all_inputs (state caller word word0 word1 : UInt64) :
    capabilityReuseDemo state caller word word0 word1 =
      modelExpected state caller word word0 word1 := by
  exact exported_adapter_refines_authoritative_all_inputs state caller word word0 word1

theorem invalid_state_five_rejects_all_inputs (caller word word0 word1 : UInt64) :
    capabilityReuseDemo 5 caller word word0 word1 = 0 := by
  simp [capabilityReuseDemo, scenarioTransition]

/-- The scalar encoding is checked against the canonical decoder and shared
capability/endpoint operations at every successful scenario transition. -/
theorem canonical_scenario_steps_agree :
    scenarioTransition 0 1 staleWord payload.word0 payload.word1 =
      authoritativeScenarioTransition 0 1 staleWord payload.word0 payload.word1 ∧
    scenarioTransition 1 1 staleWord payload.word0 payload.word1 =
      authoritativeScenarioTransition 1 1 staleWord payload.word0 payload.word1 ∧
    scenarioTransition 2 1 staleWord payload.word0 payload.word1 =
      authoritativeScenarioTransition 2 1 staleWord payload.word0 payload.word1 ∧
    scenarioTransition 3 1 currentWord payload.word0 payload.word1 =
      authoritativeScenarioTransition 3 1 currentWord payload.word0 payload.word1 ∧
    scenarioTransition 4 1 (4 * 65536) payload.word0 payload.word1 =
      authoritativeScenarioTransition 4 1 (4 * 65536) payload.word0 payload.word1 ∧
    scenarioTransition 6 1 0 payload.word0 payload.word1 =
      authoritativeScenarioTransition 6 1 0 payload.word0 payload.word1 := by
  exact ⟨scenarioTransition_refines_authoritative_all_inputs ..,
    scenarioTransition_refines_authoritative_all_inputs ..,
    scenarioTransition_refines_authoritative_all_inputs ..,
    scenarioTransition_refines_authoritative_all_inputs ..,
    scenarioTransition_refines_authoritative_all_inputs ..,
    scenarioTransition_refines_authoritative_all_inputs ..⟩

theorem words_reuse_exact_slot :
    staleHandle.slot = currentHandle.slot ∧ staleHandle.identity ≠ currentHandle.identity := by
  decide

theorem initial_word_accepted :
    (sendWord withSender 1 staleWord payload).result = .accepted := by
  native_decide

theorem initial_word_targets_original :
    (sendWord withSender 1 staleWord payload).state.mailbox 10 =
      some { endpoint := 10, sender := 1, payload } := by
  native_decide

theorem cleared_slot_rejects_old_word :
    (sendWord revoked 1 staleWord payload).result = .rejected .staleHandle := by
  native_decide

theorem cleared_slot_rejection_preserves_state :
    (sendWord revoked 1 staleWord payload).state = revoked := by
  rfl

theorem stale_word_rejected :
    (sendWord reusedState 1 staleWord payload).result = .rejected .staleHandle := by
  native_decide

theorem stale_word_preserves_state :
    (sendWord reusedState 1 staleWord payload).state = reusedState := by
  rfl

theorem another_subject_rejected :
    (sendWord reusedState 0 currentWord payload).result = .rejected .staleHandle := by
  native_decide

theorem malformed_word_rejected :
    (sendWord reusedState 1 18446744073709551615 payload).result =
      .rejected .staleHandle := by
  native_decide

theorem malformed_word_preserves_state :
    (sendWord reusedState 1 18446744073709551615 payload).state = reusedState := by
  rfl

theorem current_word_accepted :
    (sendWord reusedState 1 currentWord payload).result = .accepted := by
  native_decide

theorem current_word_targets_replacement :
    (sendWord reusedState 1 currentWord payload).state.mailbox 11 =
      some { endpoint := 11, sender := 1, payload } := by
  native_decide

theorem adapter_sequence_agrees :
    capabilityReuseDemo 0 1 staleWord payload.word0 payload.word1 =
      encodeScenarioEvent 1 1 11 staleHandle 10 ∧
    capabilityReuseDemo 1 1 staleWord payload.word0 payload.word1 =
      encodeScenarioEvent 2 2 15 currentHandle 11 ∧
    capabilityReuseDemo 2 1 staleWord payload.word0 payload.word1 =
      encodeScenarioEvent 3 3 8 staleHandle 11 ∧
    capabilityReuseDemo 2 0 currentWord payload.word0 payload.word1 = 0 ∧
    capabilityReuseDemo 3 1 currentWord payload.word0 payload.word1 =
      encodeScenarioEvent 4 4 5 currentHandle 11 ∧
    capabilityReuseDemo 5 1 currentWord payload.word0 payload.word1 = 0 ∧
    encodeOutcome (sendWord withSender 1 staleWord payload) payload = 11 ∧
    encodeOutcome (sendWord revoked 1 staleWord payload) payload = 8 ∧
    encodeOutcome (sendWord reusedState 1 staleWord payload) payload = 8 ∧
    encodeOutcome (sendWord reusedState 1 currentWord payload) payload = 5 := by
  native_decide

end LeanOS.CapabilityReuse
