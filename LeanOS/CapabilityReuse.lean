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

def staleWord : UInt64 := (CapabilityHandle.encode staleHandle).getD 0
def currentWord : UInt64 := (CapabilityHandle.encode currentHandle).getD 0

/-- Userspace-facing adapter: decode the canonical word, then use the shared
generation-aware endpoint consumer in trusted caller context. -/
def sendWord (state : EndpointIPC.State) (caller : Capability.SubjectId)
    (word : UInt64) (message : EndpointIPC.Payload) : EndpointIPC.Outcome EndpointIPC.SendError :=
  match CapabilityHandle.decode word with
  | .error _ => EndpointIPC.reject state .staleHandle
  | .ok handle => EndpointIPC.sendHandle state caller handle message

theorem words_reuse_exact_slot :
    staleHandle.slot = currentHandle.slot ∧ staleHandle.identity ≠ currentHandle.identity := by
  decide

theorem stale_word_rejected :
    (sendWord reusedState 1 staleWord payload).result = .rejected .staleHandle := by
  native_decide

theorem stale_word_preserves_state :
    (sendWord reusedState 1 staleWord payload).state = reusedState := by
  rfl

theorem current_word_accepted :
    (sendWord reusedState 1 currentWord payload).result = .accepted := by
  native_decide

theorem current_word_targets_replacement :
    (sendWord reusedState 1 currentWord payload).state.mailbox 11 =
      some { endpoint := 11, sender := 1, payload } := by
  native_decide

end LeanOS.CapabilityReuse
