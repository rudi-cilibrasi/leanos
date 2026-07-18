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
  { reusedState with
    capabilities :=
      { reusedState.capabilities with nextIdentity := CapabilityHandle.generationReserved } }

def staleWord : UInt64 := (CapabilityHandle.encode staleHandle).getD 0
def currentWord : UInt64 := (CapabilityHandle.encode currentHandle).getD 0

/-- Userspace-facing adapter: decode the canonical word, then use the shared
generation-aware endpoint consumer in trusted caller context. -/
def sendWord (state : EndpointIPC.State) (caller : Capability.SubjectId)
    (word : UInt64) (message : EndpointIPC.Payload) : EndpointIPC.Outcome EndpointIPC.SendError :=
  match CapabilityHandle.decode word with
  | .error _ => EndpointIPC.reject state .staleHandle
  | .ok handle => EndpointIPC.sendHandle state caller handle message

/-! ## Fixed-width differential-oracle adapter

The phase is a selector for one of the three exact states in the reuse
sequence, not caller-controlled kernel state: zero is the live original
authority, one is the cleared slot, and two is the same slot after fresh
installation.  The caller remains trusted entry context in the real machine
path; exposing it here lets the shared bounded corpus exercise caller binding.
-/

def phaseState (phase : UInt64) : EndpointIPC.State :=
  if phase = 0 then withSender
  else if phase = 1 then revoked
  else if phase = 3 then wrongKindState
  else reusedState

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

def modelExpected (phase caller word word0 word1 : UInt64) : UInt64 :=
  if phase = 4 then
    match (EndpointIPC.create exhaustedState 12 1 1).result with
    | .accepted => 16
    | .rejected _ => 0
  else
    let message := { word0, word1 }
    encodeOutcome (sendWord (phaseState phase) caller.toNat word message) message

/-- Allocation-free scalar implementation of the encoded reuse transition.
Unlike an accept list, it decodes every input word into its slot and generation,
then applies the phase's live-generation state before encoding observable result
and mailbox facts. -/
def capabilityReuseScalar (phase caller word : UInt64) : UInt64 :=
  if phase = 4 then 0
  else
    let slot := word % 65536
    let generation := word / 65536
    let liveGeneration := if phase = 0 then 2 else if phase = 2 then 3 else 0
    let accepted := caller = 1 && slot = 0 && liveGeneration != 0 &&
      generation = liveGeneration
    let acceptedBit := if accepted then 1 else 0
    let original := if phase = 0 && accepted then 2 else 0
    let replacement := if phase = 2 && accepted then 4 else 0
    let replacementEmpty := if phase != 2 || !accepted then 8 else 0
    acceptedBit + original + replacement + replacementEmpty

@[export leanos_capability_reuse_demo]
def capabilityReuseDemo (phase caller word _word0 _word1 : UInt64) : UInt64 :=
  capabilityReuseScalar phase caller word

theorem exported_adapter_refines_bounded_sequence :
    capabilityReuseDemo 0 1 staleWord payload.word0 payload.word1 =
      modelExpected 0 1 staleWord payload.word0 payload.word1 ∧
    capabilityReuseDemo 1 1 staleWord payload.word0 payload.word1 =
      modelExpected 1 1 staleWord payload.word0 payload.word1 ∧
    capabilityReuseDemo 2 1 staleWord payload.word0 payload.word1 =
      modelExpected 2 1 staleWord payload.word0 payload.word1 ∧
    capabilityReuseDemo 2 0 currentWord payload.word0 payload.word1 =
      modelExpected 2 0 currentWord payload.word0 payload.word1 ∧
    capabilityReuseDemo 2 1 18446744073709551615 payload.word0 payload.word1 =
      modelExpected 2 1 18446744073709551615 payload.word0 payload.word1 ∧
    capabilityReuseDemo 3 1 (4 * 65536) payload.word0 payload.word1 =
      modelExpected 3 1 (4 * 65536) payload.word0 payload.word1 ∧
    capabilityReuseDemo 4 1 0 payload.word0 payload.word1 =
      modelExpected 4 1 0 payload.word0 payload.word1 ∧
    capabilityReuseDemo 2 1 currentWord payload.word0 payload.word1 =
      modelExpected 2 1 currentWord payload.word0 payload.word1 := by
  native_decide

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
    capabilityReuseDemo 0 1 staleWord payload.word0 payload.word1 = 11 ∧
    capabilityReuseDemo 1 1 staleWord payload.word0 payload.word1 = 8 ∧
    capabilityReuseDemo 2 1 staleWord payload.word0 payload.word1 = 8 ∧
    capabilityReuseDemo 2 0 currentWord payload.word0 payload.word1 = 8 ∧
    capabilityReuseDemo 2 1 currentWord payload.word0 payload.word1 = 5 := by
  native_decide

end LeanOS.CapabilityReuse
