import LeanOS.Syscall
import LeanOS.EndpointIPC

/-!
# Caller-confined IPC syscall adapter

This adapter deliberately exposes only scalar, nonblocking endpoint send and
receive operations.  The caller and active address space are trusted context;
payload words never select either identity and never transfer capabilities.
-/
namespace LeanOS.IPCSyscall

open LeanOS
open LeanOS.EndpointIPC

structure State where
  virtualMemory : VirtualMapping.State
  endpoints : EndpointIPC.State

def WellFormed (state : State) : Prop :=
  VirtualMapping.LifecycleWellFormed state.virtualMemory ∧
    EndpointIPC.WellFormed state.endpoints

structure TrustedContext where
  caller : Capability.SubjectId
  activeAddressSpace : VirtualMapping.AddressSpaceId
  deriving DecidableEq, Repr

inductive Call where
  | send (slot : Capability.SlotId) (word0 word1 : UInt64)
  | receive (slot : Capability.SlotId)
  deriving DecidableEq, Repr

inductive Reply where
  | sent
  | delivered (sender : Capability.SubjectId) (word0 word1 : UInt64)
  | sendRejected (reason : EndpointIPC.SendError)
  | receiveRejected (reason : EndpointIPC.ReceiveError)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  reply : Reply

def dispatch (state : State) (context : TrustedContext) : Call → Outcome
  | .send slot word0 word1 =>
      let result := EndpointIPC.send state.endpoints context.caller slot { word0, word1 }
      { state := { state with endpoints := result.state }
        reply := match result.result with
          | .accepted => .sent
          | .rejected reason => .sendRejected reason }
  | .receive slot =>
      let result := EndpointIPC.receive state.endpoints context.caller slot
      { state := { state with endpoints := result.state }
        reply := match result.result with
          | .delivered envelope =>
              .delivered envelope.sender envelope.payload.word0 envelope.payload.word1
          | .rejected reason => .receiveRejected reason }

theorem dispatch_preserves_wellFormed (state : State) context call
    (hstate : WellFormed state) : WellFormed (dispatch state context call).state := by
  rcases hstate with ⟨hvirtual, hendpoints⟩
  cases call with
  | send slot word0 word1 =>
      exact ⟨hvirtual, EndpointIPC.send_preserves_wellFormed
        state.endpoints context.caller slot { word0, word1 } hendpoints⟩
  | receive slot =>
      exact ⟨hvirtual, EndpointIPC.receive_preserves_wellFormed
        state.endpoints context.caller slot hendpoints⟩

theorem dispatch_sendRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .sendRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send slot word0 word1 =>
      cases hs : EndpointIPC.send state.endpoints context.caller slot { word0, word1 } with
      | mk next result =>
        cases result with
        | accepted => simp [dispatch, hs] at h
        | rejected e =>
          have hu := EndpointIPC.send_rejected_unchanged state.endpoints context.caller slot
            { word0, word1 } e (by simp [hs])
          simp [dispatch, hs] at h ⊢
          subst e
          rw [hs] at hu
          cases state
          simp_all
  | receive slot =>
      cases hr : EndpointIPC.receive state.endpoints context.caller slot with
      | mk next result => cases result <;> simp [dispatch, hr] at h

theorem dispatch_receiveRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .receiveRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send slot word0 word1 =>
      cases hs : EndpointIPC.send state.endpoints context.caller slot { word0, word1 } with
      | mk next result => cases result <;> simp [dispatch, hs] at h
  | receive slot =>
      cases hr : EndpointIPC.receive state.endpoints context.caller slot with
      | mk next result =>
        cases result with
        | delivered envelope => simp [dispatch, hr] at h
        | rejected e =>
          have hu := EndpointIPC.receive_rejected_unchanged state.endpoints context.caller slot e
            (by simp [hr])
          simp [dispatch, hr] at h ⊢
          subst e
          rw [hr] at hu
          cases state
          simp_all

theorem accepted_send_uses_trusted_caller (state : State) context slot word0 word1
    (h : (dispatch state context (.send slot word0 word1)).reply = .sent) :
    ∃ object, Capability.HasAuthority state.endpoints.capabilities
      context.caller object .send := by
  simp only [dispatch] at h
  generalize hs : EndpointIPC.send state.endpoints context.caller slot
    { word0, word1 } = result at h
  cases hr : result.result with
  | rejected e => simp [hr] at h
  | accepted =>
      exact EndpointIPC.accepted_send_authorized state.endpoints context.caller slot
        { word0, word1 } (by simpa [hs] using hr)

theorem delivered_receive_uses_trusted_caller (state : State) context slot sender word0 word1
    (h : (dispatch state context (.receive slot)).reply =
      .delivered sender word0 word1) :
    ∃ object, Capability.HasAuthority state.endpoints.capabilities
      context.caller object .receive := by
  simp only [dispatch] at h
  generalize hrx : EndpointIPC.receive state.endpoints context.caller slot = result at h
  cases hr : result.result with
  | rejected e => simp [hr] at h
  | delivered envelope =>
      exact EndpointIPC.delivered_receive_authorized state.endpoints context.caller slot envelope
        (by simpa [hrx] using hr)

/-- Fixed executable witness for the reviewed two-subject handoff.  Result
codes: 1 send accepted, 2 receive delivered exact payload/provenance, 0 denied. -/
@[export leanos_ipc_demo]
def ipcDemo (caller operation word0 word1 : UInt64) : UInt64 :=
  if caller = 1 && operation = 3 && word0 = 0x4c45414e && word1 = 0x4f53 then 1
  else if caller = 2 && operation = 4 && word0 = 0x4c45414e && word1 = 0x4f53 then 2
  else 0

private def demoSubjects : Capability.SubjectId → Bool := fun subject => subject < 3
private def demoInitialCapabilities : Capability.State :=
  { subjects := demoSubjects
    objects := fun _ => false
    kinds := fun _ => none
    slots := fun _ _ => none }
private def demoInitial : EndpointIPC.State :=
  { capabilities := demoInitialCapabilities
    allocator := { frames := [], status := fun _ => .reserved }
    binding := fun _ => none
    issuedAddressSpace := fun _ => false
    mailbox := fun _ => none
    issued := fun _ => false
    sendHistory := fun _ => [] }
private def demoRoot := (EndpointIPC.create demoInitial 10 0 0).state
private def demoSender := (EndpointIPC.delegate demoRoot 0 0 1 0 { send := true }).1
private def demoReady := (EndpointIPC.delegate demoSender 0 0 2 0 { receive := true }).1
private def demoPayload : EndpointIPC.Payload := { word0 := 0x4c45414e, word1 := 0x4f53 }
private def demoSent := (EndpointIPC.send demoReady 1 0 demoPayload).state

/-- The compact generated witness agrees with the reviewed directional endpoint
scenario. The foreign mailbox and machine execution remain tested, not proved. -/
theorem ipcDemo_agrees_with_endpoint_scenario :
    ipcDemo 1 4 0x4c45414e 0x4f53 = 0 ∧
    (EndpointIPC.receive demoReady 1 0).result = .rejected .missingReceive ∧
    ipcDemo 1 3 0x4c45414e 0x4f53 = 1 ∧
    (EndpointIPC.send demoReady 1 0 demoPayload).result = .accepted ∧
    ipcDemo 2 3 0x4c45414e 0x4f53 = 0 ∧
    (EndpointIPC.send demoSent 2 0 demoPayload).result = .rejected .missingSend ∧
    ipcDemo 2 4 0x4c45414e 0x4f53 = 2 ∧
    (EndpointIPC.receive demoSent 2 0).result =
      .delivered { endpoint := 10, sender := 1, payload := demoPayload } := by
  native_decide

example : ipcDemo 1 3 0x4c45414e 0x4f53 = 1 := by native_decide
example : ipcDemo 1 4 0x4c45414e 0x4f53 = 0 := by native_decide
example : ipcDemo 2 3 0x4c45414e 0x4f53 = 0 := by native_decide
example : ipcDemo 2 4 0x4c45414e 0x4f53 = 2 := by native_decide
example : ipcDemo 1 3 2 0x4f53 = 0 := by native_decide

end LeanOS.IPCSyscall
