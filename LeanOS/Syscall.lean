import LeanOS.VirtualMapping

/-!
# Caller-confined syscall model

This total, fixed-width decoder separates trusted kernel call context from
untrusted scalar words.  The first vocabulary routes map, unmap, and access
checks to `VirtualMapping`; callers cannot supply either their identity or the
active address space.
-/
namespace LeanOS.Syscall

open LeanOS
open LeanOS.VirtualMapping

/-- Identity established by the (unmodeled) kernel entry path. -/
structure TrustedContext where
  caller : SubjectId
  activeAddressSpace : AddressSpaceId
  deriving DecidableEq, Repr

/-- Four ABI-independent, fixed-width words supplied by an untrusted caller. -/
structure UntrustedCall where
  number : UInt64
  arg0 : UInt64
  arg1 : UInt64
  arg2 : UInt64
  deriving DecidableEq, Repr

inductive DecodedCall where
  | map (slot : SlotId) (page : VirtualPage) (permissions : Permissions)
  | unmap (page : VirtualPage)
  | access (page : VirtualPage) (access : Access)
  deriving DecidableEq, Repr

inductive DecodeError where | unknownSyscall | malformedArguments
  deriving DecidableEq, Repr

inductive Error where
  | decode (reason : DecodeError)
  | map (reason : MapError)
  | unmap (reason : UnmapError)
  | access (reason : TranslationError)
  deriving DecidableEq, Repr

inductive Reply where | accepted | rejected (reason : Error)
  deriving DecidableEq, Repr

structure Outcome where
  state : State
  reply : Reply

def decodePermissions (word : UInt64) : Option Permissions :=
  if word = 1 then some { read := true }
  else if word = 2 then some { write := true }
  else if word = 3 then some { read := true, write := true }
  else none

/-- Numbers are explicit; an extension cannot accidentally gain a privileged default. -/
def decode (call : UntrustedCall) : Except DecodeError DecodedCall :=
  if call.number = 0 then
    match decodePermissions call.arg2 with
    | some permissions => .ok (.map call.arg0.toNat call.arg1.toNat permissions)
    | none => .error .malformedArguments
  else if call.number = 1 then
    if call.arg1 = 0 && call.arg2 = 0 then .ok (.unmap call.arg0.toNat)
    else .error .malformedArguments
  else if call.number = 2 then
    if call.arg2 != 0 then .error .malformedArguments
    else if call.arg1 = 0 then .ok (.access call.arg0.toNat .read)
    else if call.arg1 = 1 then .ok (.access call.arg0.toNat .write)
    else .error .malformedArguments
  else .error .unknownSyscall

def dispatchDecoded (state : State) (context : TrustedContext) : DecodedCall → Outcome
  | .map slot page permissions =>
      let outcome := VirtualMapping.map state context.caller slot
        context.activeAddressSpace page permissions
      { state := outcome.state, reply := match outcome.result with
        | .accepted => .accepted | .rejected reason => .rejected (.map reason) }
  | .unmap page =>
      let outcome := VirtualMapping.unmap state context.caller
        context.activeAddressSpace page
      { state := outcome.state, reply := match outcome.result with
        | .accepted => .accepted | .rejected reason => .rejected (.unmap reason) }
  | .access page access =>
      match VirtualMapping.translate state context.caller context.activeAddressSpace page access with
      | .ok _ => { state, reply := .accepted }
      | .error reason => { state, reply := .rejected (.access reason) }

def dispatch (state : State) (context : TrustedContext) (call : UntrustedCall) : Outcome :=
  match decode call with
  | .error reason => { state, reply := .rejected (.decode reason) }
  | .ok operation => dispatchDecoded state context operation

/-- The functional decoder has one unambiguous result for every input. -/
theorem decode_deterministic (call : UntrustedCall) (first second : DecodedCall)
    (hfirst : decode call = .ok first) (hsecond : decode call = .ok second) : first = second := by
  rw [hfirst] at hsecond
  exact Except.ok.inj hsecond

/-- Attacker-controlled words cannot change the caller used for authorization. -/
theorem attacker_words_cannot_change_caller (context : TrustedContext)
    (first second : UntrustedCall) :
    (context.caller, first.number).1 = (context.caller, second.number).1 := by
  rfl

theorem map_capabilities_unchanged (state : State) actor slot addressSpace page permissions :
    (VirtualMapping.map state actor slot addressSpace page permissions).state.memory.capabilities =
      state.memory.capabilities := by
  simp only [VirtualMapping.map]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  next cap =>
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    next frame => split <;> rfl

theorem unmap_capabilities_unchanged (state : State) actor addressSpace page :
    (VirtualMapping.unmap state actor addressSpace page).state.memory.capabilities =
      state.memory.capabilities := by
  simp only [VirtualMapping.unmap]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem dispatchDecoded_capabilities_unchanged (state : State) context operation :
    (dispatchDecoded state context operation).state.memory.capabilities =
      state.memory.capabilities := by
  cases operation with
  | map slot page permissions =>
      exact map_capabilities_unchanged state context.caller slot
        context.activeAddressSpace page permissions
  | unmap page =>
      exact unmap_capabilities_unchanged state context.caller context.activeAddressSpace page
  | access page access =>
      simp only [dispatchDecoded]
      split <;> rfl

theorem dispatch_capabilities_unchanged (state : State) context call :
    (dispatch state context call).state.memory.capabilities = state.memory.capabilities := by
  simp only [dispatch]
  split <;> try rfl
  exact dispatchDecoded_capabilities_unchanged state context _

/-- No subject gains capability authority through syscall dispatch. -/
theorem dispatch_authority_provenance (state : State) context call subject object right
    (hauthority : Capability.HasAuthority
      (dispatch state context call).state.memory.capabilities subject object right) :
    Capability.HasAuthority state.memory.capabilities subject object right := by
  simpa [dispatch_capabilities_unchanged state context call] using hauthority

theorem dispatchDecoded_preserves_lifecycleWellFormed (state : State) context operation
    (hstate : LifecycleWellFormed state) :
    LifecycleWellFormed (dispatchDecoded state context operation).state := by
  cases operation with
  | map slot page permissions =>
      exact map_preserves_lifecycleWellFormed state context.caller slot
        context.activeAddressSpace page permissions hstate
  | unmap page =>
      exact unmap_preserves_lifecycleWellFormed state context.caller
        context.activeAddressSpace page hstate
  | access page access =>
      simp only [dispatchDecoded]
      split <;> exact hstate

/-- Every syscall, accepted or rejected, preserves the complete composite invariant. -/
theorem dispatch_preserves_lifecycleWellFormed (state : State) context call
    (hstate : LifecycleWellFormed state) :
    LifecycleWellFormed (dispatch state context call).state := by
  simp only [dispatch]
  split <;> try simpa using hstate
  exact dispatchDecoded_preserves_lifecycleWellFormed state context _ hstate

/-- Every typed rejection, including decoding failure, preserves the complete state. -/
theorem dispatch_rejected_unchanged (state : State) context call reason
    (h : (dispatch state context call).reply = .rejected reason) :
    (dispatch state context call).state = state := by
  cases hdecode : decode call with
  | error decodeReason => simp [dispatch, hdecode]
  | ok operation =>
    cases operation with
    | map slot page permissions =>
        simp only [dispatch, hdecode, dispatchDecoded] at h ⊢
        generalize houtcome : VirtualMapping.map state context.caller slot
          context.activeAddressSpace page permissions = outcome
        cases hresult : outcome.result with
        | accepted => simp [houtcome, hresult] at h
        | rejected mapReason =>
            have hrejected :
                (VirtualMapping.map state context.caller slot context.activeAddressSpace page
                  permissions).result = .rejected mapReason := by
              simpa [houtcome] using hresult
            simpa [houtcome, hresult] using map_rejected_unchanged state context.caller slot
              context.activeAddressSpace page permissions mapReason hrejected
    | unmap page =>
        simp only [dispatch, hdecode, dispatchDecoded] at h ⊢
        generalize houtcome : VirtualMapping.unmap state context.caller
          context.activeAddressSpace page = outcome
        cases hresult : outcome.result with
        | accepted => simp [houtcome, hresult] at h
        | rejected unmapReason =>
            have hrejected :
                (VirtualMapping.unmap state context.caller context.activeAddressSpace page).result =
                  .rejected unmapReason := by
              simpa [houtcome] using hresult
            simpa [houtcome, hresult] using unmap_rejected_unchanged state context.caller
              context.activeAddressSpace page unmapReason hrejected
    | access page access =>
        simp only [dispatch, hdecode, dispatchDecoded]
        split <;> rfl

/-- A non-owner cannot mutate the address space selected by trusted context. -/
theorem nonowner_dispatchDecoded_unchanged (state : State) context operation owner
    (howner : state.owner context.activeAddressSpace = some owner)
    (hne : context.caller ≠ owner) :
    (dispatchDecoded state context operation).state = state := by
  cases operation with
  | map slot page permissions =>
      have hne' : owner ≠ context.caller := Ne.symm hne
      simp [dispatchDecoded, VirtualMapping.map, VirtualMapping.reject, howner, hne']
  | unmap page =>
      have hne' : owner ≠ context.caller := Ne.symm hne
      simp [dispatchDecoded, VirtualMapping.unmap, VirtualMapping.reject, howner, hne']
  | access page access =>
      simp only [dispatchDecoded]
      split <;> rfl

private def subjects : SubjectId → Bool := fun subject => subject < 2
private def capabilities : Capability.State :=
  { subjects
    objects := fun object => object = 10
    kinds := fun object => if object = 10 then some .memory else none
    slots := fun subject slot =>
      if subject = 0 ∧ slot = 0 then
        some { object := 10, kind := .memory, rights := Capability.allRights }
      else none }
private def memory : MemoryLifecycle.State :=
  { capabilities
    allocator := { frames := [4], status := fun frame => if frame = 4 then .owned 10 else .reserved }
    binding := fun object => if object = 10 then some 4 else none
    issued := fun object => object = 10 }
private def initial : State :=
  { memory
    owner := fun space => if space = 5 then some 0 else if space = 6 then some 1 else none
    mappings := fun _ _ => none
    issuedAddressSpace := fun space => space = 5 || space = 6 }
private def caller0 : TrustedContext := { caller := 0, activeAddressSpace := 5 }
private def caller1Space : TrustedContext := { caller := 0, activeAddressSpace := 6 }
private def mapRead : UntrustedCall := { number := 0, arg0 := 0, arg1 := 7, arg2 := 1 }
private def mapped := (dispatch initial caller0 mapRead).state

-- Valid caller-confined operation and access check.
example : (dispatch initial caller0 mapRead).reply = .accepted := by native_decide
example : (dispatch mapped caller0 { number := 2, arg0 := 7, arg1 := 0, arg2 := 0 }).reply =
    .accepted := by native_decide
-- An attacker cannot forge subject/address-space identity with scalar words.
example : (dispatch initial caller1Space mapRead).reply = .rejected (.map .notOwner) := by
  native_decide
example : (dispatch initial caller0 { number := 0, arg0 := 1, arg1 := 5, arg2 := 1 }).reply =
    .rejected (.map .staleSlot) := by native_decide
-- Unknown numbers and malformed permission bits are typed, state-preserving failures.
example : (dispatch initial caller0 { number := 99, arg0 := 0, arg1 := 0, arg2 := 0 }).reply =
    .rejected (.decode .unknownSyscall) := by native_decide
example : (dispatch initial caller0 { number := 0, arg0 := 0, arg1 := 7, arg2 := 4 }).reply =
    .rejected (.decode .malformedArguments) := by native_decide
-- Cross-address-space unmap and replay against a destroyed-space state fail closed.
example : (dispatch mapped { caller := 1, activeAddressSpace := 5 }
    { number := 1, arg0 := 7, arg1 := 0, arg2 := 0 }).reply =
    .rejected (.unmap .notOwner) := by native_decide
private def destroyed : State := { mapped with owner := fun _ => none, mappings := fun _ _ => none }
example : (dispatch destroyed caller0 mapRead).reply = .rejected (.map .invalidAddressSpace) := by
  native_decide

end LeanOS.Syscall
