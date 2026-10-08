import LeanOS.SecurityClaims

open LeanOS Capability EndpointDirectory

/- A directory that hands out receive rights along with send must break the
no-amplification claim: its attenuation policy is not a subset of send-only,
so the claim cannot be instantiated for it. -/
def sendAndReceive : Rights := { send := true, receive := true }

example (st : State) (d : Directory) (client : SubjectId) (clientSlot : SlotId)
    (name : Name) (candidate : SubjectId) (object : ObjectId)
    (hauthority : HasAuthority (resolveWith sendAndReceive st d client clientSlot name).1
      candidate object .receive) :
    HasAuthority st candidate object .receive ∨
      (candidate = client ∧ Right.receive = .send ∧
        HasAuthority st d.subject object .send ∧ HasAuthority st d.subject object .grant) :=
  (SecurityClaims.endpoint_directory_no_amplification sendAndReceive rfl st d client
    clientSlot name).1 candidate object .receive hauthority
