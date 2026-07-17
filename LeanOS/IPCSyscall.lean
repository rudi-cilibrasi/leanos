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
  | send (handleWord : UInt64) (word0 word1 : UInt64)
  | receive (handleWord : UInt64)
  deriving DecidableEq, Repr

inductive Reply where
  | sent
  | delivered (sender : Capability.SubjectId) (word0 word1 : UInt64)
  | sendHandleRejected (reason : CapabilityHandle.WordResolveDenial)
  | sendRejected (reason : EndpointIPC.SendError)
  | receiveHandleRejected (reason : CapabilityHandle.WordResolveDenial)
  | receiveRejected (reason : EndpointIPC.ReceiveError)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  reply : Reply

def dispatch (state : State) (context : TrustedContext) : Call → Outcome
  | .send handleWord word0 word1 =>
      match CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | .error reason => { state, reply := .sendHandleRejected reason }
      | .ok resolution =>
          let result := EndpointIPC.send state.endpoints context.caller
            resolution.handle.slot { word0, word1 }
          { state := { state with endpoints := result.state }
            reply := match result.result with
              | .accepted => .sent
              | .rejected reason => .sendRejected reason }
  | .receive handleWord =>
      match CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | .error reason => { state, reply := .receiveHandleRejected reason }
      | .ok resolution =>
          let result := EndpointIPC.receive state.endpoints context.caller
            resolution.handle.slot
          { state := { state with endpoints := result.state }
            reply := match result.result with
              | .delivered envelope =>
                  .delivered envelope.sender envelope.payload.word0 envelope.payload.word1
              | .rejected reason => .receiveRejected reason }

theorem dispatch_preserves_wellFormed (state : State) context call
    (hstate : WellFormed state) : WellFormed (dispatch state context call).state := by
  rcases hstate with ⟨hvirtual, hendpoints⟩
  cases call with
  | send handleWord word0 word1 =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error reason =>
          simpa [WellFormed, dispatch, hresolve] using And.intro hvirtual hendpoints
      | ok resolution =>
          simpa [WellFormed, dispatch, hresolve] using And.intro hvirtual
            (EndpointIPC.send_preserves_wellFormed state.endpoints context.caller
              resolution.handle.slot { word0, word1 } hendpoints)
  | receive handleWord =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error reason =>
          simpa [WellFormed, dispatch, hresolve] using And.intro hvirtual hendpoints
      | ok resolution =>
          simpa [WellFormed, dispatch, hresolve] using And.intro hvirtual
            (EndpointIPC.receive_preserves_wellFormed state.endpoints context.caller
              resolution.handle.slot hendpoints)

theorem dispatch_sendHandleRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .sendHandleRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send handleWord word0 word1 =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve]
      | ok resolution =>
          cases hs : EndpointIPC.send state.endpoints context.caller resolution.handle.slot
            { word0, word1 } with
          | mk next result => cases result <;> simp [dispatch, hresolve, hs] at h
  | receive handleWord =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hr : EndpointIPC.receive state.endpoints context.caller
            resolution.handle.slot with
          | mk next result => cases result <;> simp [dispatch, hresolve, hr] at h

theorem dispatch_receiveHandleRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .receiveHandleRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send handleWord word0 word1 =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hs : EndpointIPC.send state.endpoints context.caller resolution.handle.slot
            { word0, word1 } with
          | mk next result => cases result <;> simp [dispatch, hresolve, hs] at h
  | receive handleWord =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve]
      | ok resolution =>
          cases hr : EndpointIPC.receive state.endpoints context.caller
            resolution.handle.slot with
          | mk next result => cases result <;> simp [dispatch, hresolve, hr] at h

theorem dispatch_sendRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .sendRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send handleWord word0 word1 =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hs : EndpointIPC.send state.endpoints context.caller resolution.handle.slot
            { word0, word1 } with
          | mk next result =>
            cases result with
            | accepted => simp [dispatch, hresolve, hs] at h
            | rejected e =>
              have hu := EndpointIPC.send_rejected_unchanged state.endpoints context.caller
                resolution.handle.slot { word0, word1 } e (by simp [hs])
              simp [dispatch, hresolve, hs] at h ⊢
              subst e
              rw [hs] at hu
              cases state
              simp_all
  | receive handleWord =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hr : EndpointIPC.receive state.endpoints context.caller
            resolution.handle.slot with
          | mk next result => cases result <;> simp [dispatch, hresolve, hr] at h

theorem dispatch_receiveRejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .receiveRejected reason) :
    (dispatch state context call).state = state := by
  cases call with
  | send handleWord word0 word1 =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hs : EndpointIPC.send state.endpoints context.caller resolution.handle.slot
            { word0, word1 } with
          | mk next result => cases result <;> simp [dispatch, hresolve, hs] at h
  | receive handleWord =>
      cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint with
      | error denial => simp [dispatch, hresolve] at h
      | ok resolution =>
          cases hr : EndpointIPC.receive state.endpoints context.caller
            resolution.handle.slot with
          | mk next result =>
            cases result with
            | delivered envelope => simp [dispatch, hresolve, hr] at h
            | rejected e =>
              have hu := EndpointIPC.receive_rejected_unchanged state.endpoints context.caller
                resolution.handle.slot e (by simp [hr])
              simp [dispatch, hresolve, hr] at h ⊢
              subst e
              rw [hr] at hu
              cases state
              simp_all

theorem accepted_send_uses_trusted_caller (state : State) context handleWord word0 word1
    (h : (dispatch state context (.send handleWord word0 word1)).reply = .sent) :
    ∃ object, Capability.HasAuthority state.endpoints.capabilities
      context.caller object .send := by
  cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
    { caller := context.caller } handleWord .endpoint with
  | error denial => simp [dispatch, hresolve] at h
  | ok resolution =>
      generalize hs : EndpointIPC.send state.endpoints context.caller
        resolution.handle.slot { word0, word1 } = result at h
      cases hr : result.result with
      | rejected e => simp [dispatch, hresolve, hs, hr] at h
      | accepted =>
          exact EndpointIPC.accepted_send_authorized state.endpoints context.caller
            resolution.handle.slot { word0, word1 } (by simpa [hs] using hr)

theorem delivered_receive_uses_trusted_caller (state : State) context handleWord sender word0 word1
    (h : (dispatch state context (.receive handleWord)).reply =
      .delivered sender word0 word1) :
    ∃ object, Capability.HasAuthority state.endpoints.capabilities
      context.caller object .receive := by
  cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
    { caller := context.caller } handleWord .endpoint with
  | error denial => simp [dispatch, hresolve] at h
  | ok resolution =>
      generalize hrx : EndpointIPC.receive state.endpoints context.caller
        resolution.handle.slot = result at h
      cases hr : result.result with
      | rejected e => simp [dispatch, hresolve, hrx, hr] at h
      | delivered envelope =>
          exact EndpointIPC.delivered_receive_authorized state.endpoints context.caller
            resolution.handle.slot envelope (by simpa [hrx] using hr)

/-- Every accepted userspace send resolved the complete opaque word to the
exact live endpoint-capability generation in the trusted caller's space. -/
theorem accepted_send_resolves_exact (state : State) context handleWord word0 word1
    (h : (dispatch state context (.send handleWord word0 word1)).reply = .sent) :
    ∃ handle capability,
      CapabilityHandle.decode handleWord = .ok handle ∧
      state.endpoints.capabilities.subjects context.caller = true ∧
      Capability.slotInRange state.endpoints.capabilities context.caller handle.slot = true ∧
      state.endpoints.capabilities.slots context.caller handle.slot = some capability ∧
      capability.identity = handle.identity ∧ capability.kind = .endpoint ∧
      state.endpoints.capabilities.objects capability.object = true ∧
      state.endpoints.capabilities.kinds capability.object = some .endpoint := by
  cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
    { caller := context.caller } handleWord .endpoint with
  | error denial => simp [dispatch, hresolve] at h
  | ok resolution =>
      rcases CapabilityHandle.resolveCurrent_sound state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint resolution hresolve with
        ⟨hdecode, hsubject, hrange, hslot, hidentity, hkind, hlive, hkinds⟩
      exact ⟨resolution.handle, resolution.capability, hdecode, hsubject, hrange,
        hslot, hidentity, hkind, hlive, hkinds⟩

/-- Every delivered userspace receive resolved the complete opaque word to the
exact live endpoint-capability generation in the trusted caller's space. -/
theorem delivered_receive_resolves_exact (state : State) context handleWord sender word0 word1
    (h : (dispatch state context (.receive handleWord)).reply =
      .delivered sender word0 word1) :
    ∃ handle capability,
      CapabilityHandle.decode handleWord = .ok handle ∧
      state.endpoints.capabilities.subjects context.caller = true ∧
      Capability.slotInRange state.endpoints.capabilities context.caller handle.slot = true ∧
      state.endpoints.capabilities.slots context.caller handle.slot = some capability ∧
      capability.identity = handle.identity ∧ capability.kind = .endpoint ∧
      state.endpoints.capabilities.objects capability.object = true ∧
      state.endpoints.capabilities.kinds capability.object = some .endpoint := by
  cases hresolve : CapabilityHandle.resolveCurrent state.endpoints.capabilities
    { caller := context.caller } handleWord .endpoint with
  | error denial => simp [dispatch, hresolve] at h
  | ok resolution =>
      rcases CapabilityHandle.resolveCurrent_sound state.endpoints.capabilities
        { caller := context.caller } handleWord .endpoint resolution hresolve with
        ⟨hdecode, hsubject, hrange, hslot, hidentity, hkind, hlive, hkinds⟩
      exact ⟨resolution.handle, resolution.capability, hdecode, hsubject, hrange,
        hslot, hidentity, hkind, hlive, hkinds⟩

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
private def demoAdapterState : State :=
  { virtualMemory :=
      { memory :=
          { capabilities := demoReady.capabilities
            allocator := demoReady.allocator
            binding := demoReady.binding
            issued := demoReady.issued }
        owner := fun _ => none
        mappings := fun _ _ => none
        issuedAddressSpace := demoReady.issuedAddressSpace }
    endpoints := demoReady }
private def demoSenderHandleWord : UInt64 := 2 * 65536
private def demoReceiverHandleWord : UInt64 := 3 * 65536
private def demoAdapterSent :=
  (dispatch demoAdapterState { caller := 1, activeAddressSpace := 0 }
    (.send demoSenderHandleWord demoPayload.word0 demoPayload.word1)).state

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

-- Userspace IPC dispatch accepts only the current endpoint generation in the
-- trusted caller's capability space and preserves typed malformed/stale errors.
example :
    (dispatch demoAdapterState { caller := 1, activeAddressSpace := 0 }
      (.send demoSenderHandleWord demoPayload.word0 demoPayload.word1)).reply = .sent := by
  native_decide
example :
    (dispatch demoAdapterSent { caller := 2, activeAddressSpace := 0 }
      (.receive demoReceiverHandleWord)).reply =
        .delivered 1 demoPayload.word0 demoPayload.word1 := by
  native_decide
example :
    (dispatch demoAdapterState { caller := 1, activeAddressSpace := 0 }
      (.send (4 * 65536) demoPayload.word0 demoPayload.word1)).reply =
        .sendHandleRejected (.denied .staleHandle) := by
  native_decide
example :
    (dispatch demoAdapterState { caller := 2, activeAddressSpace := 0 }
      (.send demoSenderHandleWord demoPayload.word0 demoPayload.word1)).reply =
        .sendHandleRejected (.denied .staleHandle) := by
  native_decide
example :
    (dispatch demoAdapterState { caller := 1, activeAddressSpace := 0 }
      (.send (demoSenderHandleWord + 65535) demoPayload.word0 demoPayload.word1)).reply =
        .sendHandleRejected (.malformed .reservedSlot) := by
  native_decide

example : ipcDemo 1 3 0x4c45414e 0x4f53 = 1 := by native_decide
example : ipcDemo 1 4 0x4c45414e 0x4f53 = 0 := by native_decide
example : ipcDemo 2 3 0x4c45414e 0x4f53 = 0 := by native_decide
example : ipcDemo 2 4 0x4c45414e 0x4f53 = 2 := by native_decide
example : ipcDemo 1 3 2 0x4f53 = 0 := by native_decide

end LeanOS.IPCSyscall
