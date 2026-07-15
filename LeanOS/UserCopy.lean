import LeanOS.X86PageTable
import LeanOS.Syscall

/-!
# Bounded user-memory copies

A small sequential byte model.  Every byte is prevalidated through
`VirtualMapping.translate`; kernel buffers are typed identifiers rather than
addresses. Multiple virtual pages in one range may not resolve to the same
physical frame, so accepted writes have an unambiguous exact-byte footprint.
-/
namespace LeanOS.UserCopy

open LeanOS
open LeanOS.VirtualMapping

abbrev BufferId := Nat
abbrev ByteOffset := Nat

def maxCopyBytes : Nat := 16
def addressLimit : Nat := 2 ^ 64
def canonicalByteLimit : Nat := X86PageTable.lowerCanonicalPages * X86PageTable.pageBytes

structure TrustedContext where
  caller : SubjectId
  activeAddressSpace : AddressSpaceId
  deriving BEq, DecidableEq, Repr

structure Location where
  virtualPage : VirtualPage
  frame : FrameAllocator.FrameId
  offset : ByteOffset
  deriving BEq, DecidableEq, Repr

structure State where
  virtual : VirtualMapping.State
  userBytes : FrameAllocator.FrameId -> ByteOffset -> UInt8
  kernelBytes : BufferId -> ByteOffset -> UInt8

inductive CopyError where
  | tooLong | overflow | nonCanonical | aliased
  | translation (reason : TranslationError)
  deriving BEq, DecidableEq, Repr

inductive Result where | accepted | rejected (reason : CopyError)
  deriving BEq, DecidableEq, Repr

structure Outcome where
  state : State
  result : Result

def reject (state : State) (reason : CopyError) : Outcome :=
  { state, result := .rejected reason }

def byteLocation (state : State) (context : TrustedContext) (address : Nat)
    (access : Access) : Except CopyError Location := do
  let virtualPage := address / X86PageTable.pageBytes
  let frame <- (translate state.virtual context.caller context.activeAddressSpace virtualPage access).mapError
    .translation
  pure { virtualPage, frame, offset := address % X86PageTable.pageBytes }

def hasFrameAlias (previous : List Location) (location : Location) : Bool :=
  previous.any fun candidate =>
    candidate.frame == location.frame && candidate.virtualPage != location.virtualPage

def validateLoop (state : State) (context : TrustedContext) (start : Nat)
    (access : Access) : Nat -> Except CopyError (List Location)
  | 0 => .ok []
  | n + 1 =>
      match validateLoop state context start access n with
      | .error reason => .error reason
      | .ok previous =>
          match byteLocation state context (start + n) access with
          | .error reason => .error reason
          | .ok location =>
              if hasFrameAlias previous location then .error .aliased
              else .ok (previous ++ [location])

/-- Validate arithmetic, canonicality, every mapping and the alias policy
before either memory domain is changed.  Zero-length copies dereference no
address and therefore accept every start value. -/
def validate (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (access : Access) : Except CopyError (List Location) :=
  if length > maxCopyBytes then .error .tooLong
  else if length = 0 then .ok []
  else if start.toNat + length > addressLimit then .error .overflow
  else if start.toNat + length > canonicalByteLimit then .error .nonCanonical
  else validateLoop state context start.toNat access length

def setKernelRange (bytes : BufferId -> ByteOffset -> UInt8) (buffer : BufferId)
    (values : List UInt8) : BufferId -> ByteOffset -> UInt8 :=
  fun candidate offset =>
    if candidate = buffer then values.getD offset (bytes candidate offset)
    else bytes candidate offset

def setUserByte (bytes : FrameAllocator.FrameId -> ByteOffset -> UInt8)
    (location : Location) (value : UInt8) :
    FrameAllocator.FrameId -> ByteOffset -> UInt8 :=
  fun frame offset => if frame = location.frame && offset = location.offset then value
    else bytes frame offset

def setUserLocations (bytes : FrameAllocator.FrameId -> ByteOffset -> UInt8) :
    List Location -> List UInt8 -> FrameAllocator.FrameId -> ByteOffset -> UInt8
  | location :: locations, value :: values =>
      setUserLocations (setUserByte bytes location value) locations values
  | _, _ => bytes

def copyFromUser (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  match validate state context start length .read with
  | .error reason => reject state reason
  | .ok locations =>
      let values := locations.map (fun location => state.userBytes location.frame location.offset)
      { state := { state with kernelBytes := setKernelRange state.kernelBytes buffer values }
        result := .accepted }

def copyToUser (state : State) (context : TrustedContext) (start : UInt64)
    (length : Nat) (buffer : BufferId) : Outcome :=
  match validate state context start length .write with
  | .error reason => reject state reason
  | .ok locations =>
      let values := List.range length |>.map (state.kernelBytes buffer)
      { state := { state with userBytes := setUserLocations state.userBytes locations values }
        result := .accepted }

theorem validate_too_long (state : State) context start length access
    (h : length > maxCopyBytes) :
    validate state context start length access = .error .tooLong := by
  simp [validate, h]

theorem validate_zero (state : State) context start access :
    validate state context start 0 access = .ok [] := by
  simp [validate, maxCopyBytes]

/-- Successful nonempty validation proves that the mathematical half-open
range fits both the fixed-width address space and the modeled canonical area. -/
theorem validate_bounds (state : State) context start length access locations
    (h : validate state context start length access = .ok locations) :
    length = 0 ∨ (start.toNat + length <= addressLimit ∧
      start.toNat + length <= canonicalByteLimit) := by
  simp only [validate] at h
  split at h <;> try contradiction
  split at h
  · simp_all
  split at h <;> try contradiction
  split at h <;> try contradiction
  right
  omega

theorem validateLoop_length (state : State) context start access length locations
    (h : validateLoop state context start access length = .ok locations) :
    locations.length = length := by
  induction length generalizing locations with
  | zero => simp [validateLoop] at h; simp_all
  | succ n ih =>
      cases hp : validateLoop state context start access n with
      | error reason => simp [validateLoop, hp] at h
      | ok previous =>
          cases hl : byteLocation state context (start + n) access with
          | error reason => simp [validateLoop, hp, hl] at h
          | ok location =>
              by_cases hc : hasFrameAlias previous location = true
              · simp [validateLoop, hp, hl, hc] at h
              · simp [validateLoop, hp, hl, hc] at h
                cases h
                simp [ih previous hp]

theorem validate_length (state : State) context start access length locations
    (h : validate state context start length access = .ok locations) :
    locations.length = length := by
  simp only [validate] at h
  split at h <;> try contradiction
  split at h
  · simp_all
  split at h <;> try contradiction
  split at h <;> try contradiction
  exact validateLoop_length state context start.toNat access length locations h

/-- Every location accepted by whole-range validation came from the current
caller-owned address space with the requested permission. -/
theorem validateLoop_authorized (state : State) context start access length locations
    (h : validateLoop state context start access length = .ok locations)
    (location : Location) (hin : location ∈ locations) :
    exists address, start <= address /\ address < start + length /\
      byteLocation state context address access = .ok location := by
  induction length generalizing locations location with
  | zero => simp [validateLoop] at h; simp_all
  | succ n ih =>
      cases hp : validateLoop state context start access n with
      | error reason => simp [validateLoop, hp] at h
      | ok previous =>
          cases hl : byteLocation state context (start + n) access with
          | error reason => simp [validateLoop, hp, hl] at h
          | ok last =>
              by_cases hc : hasFrameAlias previous last = true
              · simp [validateLoop, hp, hl, hc] at h
              · simp [validateLoop, hp, hl, hc] at h
                cases h
                simp only [List.mem_append, List.mem_singleton] at hin
                cases hin with
                | inl hold =>
                    obtain ⟨address, hlo, hhi, hauth⟩ := ih previous hp location hold
                    exact ⟨address, hlo, Nat.lt_succ_of_lt hhi, hauth⟩
                | inr heq =>
                    subst location
                    exact ⟨start + n, Nat.le_add_right start n, by omega, hl⟩

theorem copyFrom_rejected_unchanged state context start length buffer reason
    (h : (copyFromUser state context start length buffer).result = .rejected reason) :
    (copyFromUser state context start length buffer).state = state := by
  simp only [copyFromUser] at h |-
  split <;> simp_all [reject]

theorem copyTo_rejected_unchanged state context start length buffer reason
    (h : (copyToUser state context start length buffer).result = .rejected reason) :
    (copyToUser state context start length buffer).state = state := by
  simp only [copyToUser] at h |-
  split <;> simp_all [reject]

/-- Copy-from changes no user byte. -/
theorem copyFrom_preserves_user (state : State) context start length buffer :
    (copyFromUser state context start length buffer).state.userBytes = state.userBytes := by
  simp only [copyFromUser]
  split <;> rfl

/-- Copy-to changes no kernel byte. -/
theorem copyTo_preserves_kernel (state : State) context start length buffer :
    (copyToUser state context start length buffer).state.kernelBytes = state.kernelBytes := by
  simp only [copyToUser]
  split <;> rfl

/-- Updating one typed kernel buffer leaves every other buffer and every byte
beyond the supplied value list unchanged. -/
theorem setKernelRange_outside bytes buffer values candidate offset
    (h : candidate ≠ buffer ∨ values.length <= offset) :
    setKernelRange bytes buffer values candidate offset = bytes candidate offset := by
  rcases h with hbuffer | hoffset
  · simp [setKernelRange, hbuffer]
  · simp [setKernelRange, List.getD_eq_getElem?_getD, hoffset]

/-- An accepted copy-from installs exactly the bytes read from its validated
locations in the selected typed buffer. -/
theorem copyFrom_validated_exact state context start length buffer locations
    (h : validate state context start length .read = .ok locations) :
    (copyFromUser state context start length buffer).state.kernelBytes =
      setKernelRange state.kernelBytes buffer
        (locations.map fun location => state.userBytes location.frame location.offset) := by
  simp [copyFromUser, h]

/-- Copy-from cannot change another typed buffer or an offset outside the
requested length. -/
theorem copyFrom_outside state context start length buffer candidate offset
    (h : candidate ≠ buffer ∨ length <= offset) :
    (copyFromUser state context start length buffer).state.kernelBytes candidate offset =
      state.kernelBytes candidate offset := by
  simp only [copyFromUser]
  split
  · rfl
  next locations hvalidate =>
    apply setKernelRange_outside
    rcases h with hbuffer | hoffset
    · exact Or.inl hbuffer
    · right
      simpa [validate_length state context start .read length locations hvalidate] using hoffset

/-- A physical byte outside the prevalidated destination set is unchanged. -/
theorem setUserLocations_outside bytes locations values frame offset
    (h : forall location, location ∈ locations ->
      location.frame ≠ frame ∨ location.offset ≠ offset) :
    setUserLocations bytes locations values frame offset = bytes frame offset := by
  induction locations generalizing bytes values with
  | nil => simp [setUserLocations]
  | cons location locations ih =>
      cases values with
      | nil => simp [setUserLocations]
      | cons value values =>
          simp only [setUserLocations]
          rw [ih]
          · simp [setUserByte]
            rcases h location (by simp) with hframe | hoffset
            · simp [Ne.symm hframe]
            · simp [Ne.symm hoffset]
          · intro candidate hin
            exact h candidate (by simp [hin])

/-- An accepted copy-to installs exactly the selected kernel-buffer values at
the complete prevalidated destination list. -/
theorem copyTo_validated_exact state context start length buffer locations
    (h : validate state context start length .write = .ok locations) :
    (copyToUser state context start length buffer).state.userBytes =
      setUserLocations state.userBytes locations
        (List.range length |>.map (state.kernelBytes buffer)) := by
  simp [copyToUser, h]

/-- Copy-to leaves every physical byte outside its validated destination list
unchanged at the operation level. -/
theorem copyTo_outside state context start length buffer locations frame offset
    (hvalidate : validate state context start length .write = .ok locations)
    (houtside : forall location, location ∈ locations ->
      location.frame ≠ frame ∨ location.offset ≠ offset) :
    (copyToUser state context start length buffer).state.userBytes frame offset =
      state.userBytes frame offset := by
  simp [copyToUser, hvalidate, setUserLocations_outside _ _ _ _ _ houtside]

/-- A different subject cannot even resolve the first byte of an address space
owned by another subject. This is the operation's confinement root: complete
prevalidation means neither copy direction can accept such a nonempty range. -/
theorem byteLocation_other_subject_rejected state owner context address access
    (howner : state.virtual.owner context.activeAddressSpace = some owner)
    (hne : context.caller ≠ owner) :
    byteLocation state context address access = .error (.translation .notOwner) := by
  have htranslate : translate state.virtual context.caller context.activeAddressSpace
      (address / X86PageTable.pageBytes) access = .error .notOwner := by
    simp [VirtualMapping.translate, howner, Ne.symm hne]
  simp only [byteLocation]
  rw [htranslate]
  rfl

theorem validateLoop_other_subject_rejected state owner context start access length
    (howner : state.virtual.owner context.activeAddressSpace = some owner)
    (hne : context.caller ≠ owner) (hpositive : 0 < length) :
    validateLoop state context start access length =
      .error (.translation .notOwner) := by
  induction length with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simp [validateLoop,
            byteLocation_other_subject_rejected state owner context start access howner hne]
      | succ n =>
          rw [validateLoop, ih (Nat.zero_lt_succ n)]

theorem copyFrom_other_subject_rejected state owner context start length buffer
    (howner : state.virtual.owner context.activeAddressSpace = some owner)
    (hne : context.caller ≠ owner)
    (hpositive : 0 < length) (hbound : length <= maxCopyBytes)
    (hcanonical : start.toNat + length <= canonicalByteLimit) :
    (copyFromUser state context start length buffer).result =
      .rejected (.translation .notOwner) := by
  have hlimit : canonicalByteLimit <= addressLimit := by
    native_decide
  have haddress : start.toNat + length <= addressLimit := Nat.le_trans hcanonical hlimit
  have hloop := validateLoop_other_subject_rejected state owner context start.toNat .read
    length howner hne hpositive
  have hvalidate : validate state context start length .read =
      .error (.translation .notOwner) := by
    simp [validate, Nat.not_lt.mpr hbound, Nat.ne_of_gt hpositive,
      Nat.not_lt.mpr haddress, Nat.not_lt.mpr hcanonical, hloop]
  simp [copyFromUser, hvalidate, reject]

theorem copyTo_other_subject_rejected state owner context start length buffer
    (howner : state.virtual.owner context.activeAddressSpace = some owner)
    (hne : context.caller ≠ owner)
    (hpositive : 0 < length) (hbound : length <= maxCopyBytes)
    (hcanonical : start.toNat + length <= canonicalByteLimit) :
    (copyToUser state context start length buffer).result =
      .rejected (.translation .notOwner) := by
  have hlimit : canonicalByteLimit <= addressLimit := by
    native_decide
  have haddress : start.toNat + length <= addressLimit := Nat.le_trans hcanonical hlimit
  have hloop := validateLoop_other_subject_rejected state owner context start.toNat .write
    length howner hne hpositive
  have hvalidate : validate state context start length .write =
      .error (.translation .notOwner) := by
    simp [validate, Nat.not_lt.mpr hbound, Nat.ne_of_gt hpositive,
      Nat.not_lt.mpr haddress, Nat.not_lt.mpr hcanonical, hloop]
  simp [copyToUser, hvalidate, reject]

/- Executable traces exercise both pages and every rejection class. -/
private def demoVirtual : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun subject => subject = 0
            objects := fun object => object = 10 || object = 11
            kinds := fun object => if object = 10 || object = 11 then some .memory else none
            slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 then .owned 10
              else if frame = 5 then .owned 11 else .reserved }
        binding := fun object => if object = 10 then some 4 else if object = 11 then some 5 else none
        issued := fun object => object = 10 || object = 11 }
    owner := fun space => if space = 7 then some 0 else none
    mappings := fun space page =>
      if space = 7 ∧ page = 0 then some { object := 10, permissions := { read := true, write := true } }
      else if space = 7 ∧ page = 1 then some { object := 11, permissions := { read := true, write := true } }
      else none
    issuedAddressSpace := fun space => space = 7 }

private def demo : State :=
  { virtual := demoVirtual
    userBytes := fun frame offset => UInt8.ofNat (frame * 16 + offset)
    kernelBytes := fun buffer offset => UInt8.ofNat (buffer + offset + 1) }
private def ctx : TrustedContext := { caller := 0, activeAddressSpace := 7 }
private def readOnlyMappings (space page : Nat) : Option Mapping :=
  if space = 7 ∧ page = 0 then
    some { object := 10, permissions := { read := true } }
  else none
private def readOnly : State :=
  { demo with virtual := { demoVirtual with mappings := readOnlyMappings } }
private def stale : State :=
  { demo with virtual := { demoVirtual with memory :=
      { demoVirtual.memory with
        allocator := { demoVirtual.memory.allocator with
          status := fun frame => if frame = 4 then .owned 12
            else demoVirtual.memory.allocator.status frame }
        binding := fun _ => none } } }
private def aliasMappings (space page : Nat) : Option Mapping :=
  if space = 7 ∧ (page = 0 ∨ page = 1) then
    some { object := 10, permissions := { read := true, write := true } }
  else none
private def aliased : State :=
  { demo with virtual := { demoVirtual with mappings := aliasMappings } }

example : (copyFromUser demo ctx 0 0 0).result = .accepted := by native_decide
example : (copyFromUser demo ctx 0 maxCopyBytes 0).result = .accepted := by native_decide
example : (copyFromUser demo ctx 0 (maxCopyBytes + 1) 0).result = .rejected .tooLong := by native_decide
example : (copyFromUser demo ctx (UInt64.ofNat (addressLimit - 1)) 2 0).result = .rejected .overflow := by native_decide
example : (copyFromUser demo ctx (UInt64.ofNat canonicalByteLimit) 1 0).result =
    .rejected .nonCanonical := by native_decide
example : (copyFromUser demo ctx 4095 2 0).result = .accepted := by native_decide
example : (copyFromUser demo ctx 4095 2 8).state.kernelBytes 8 0 =
    demo.userBytes 4 4095 := by native_decide
example : (copyFromUser demo ctx 4095 2 8).state.kernelBytes 8 1 =
    demo.userBytes 5 0 := by native_decide
example : (copyToUser demo ctx 4095 2 8).state.userBytes 4 4095 =
    demo.kernelBytes 8 0 := by native_decide
example : (copyToUser demo ctx 4095 2 8).state.userBytes 5 0 =
    demo.kernelBytes 8 1 := by native_decide
example : (copyFromUser demo ctx 8191 2 0).result = .rejected (.translation .unmappedPage) := by native_decide
example : (copyFromUser demo ctx 8191 2 0).state = demo := by
  apply copyFrom_rejected_unchanged (reason := .translation .unmappedPage)
  native_decide
example : (copyToUser readOnly ctx 0 1 0).result = .rejected (.translation .missingPermission) := by native_decide
example : (copyFromUser aliased ctx 4095 2 0).result = .rejected .aliased := by native_decide
example : (copyFromUser stale ctx 0 1 0).result = .rejected (.translation .retiredObject) := by native_decide
example : (copyFromUser (copyToUser demo ctx 0 4 3).state ctx 0 4 9).state.kernelBytes 9 2 =
    demo.kernelBytes 3 2 := by native_decide

end LeanOS.UserCopy
