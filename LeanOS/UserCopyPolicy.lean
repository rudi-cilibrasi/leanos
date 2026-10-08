import LeanOS.UserCopy

/-!
# The booted user-copy range check, generated from Lean (issue #478)

`boot/kernel.c` used to validate every user-copy range with a handwritten
`validate_copy`. The kernel now calls `leanos_user_copy_policy`, generated from
this module, instead.

`UserCopy.validate` is the model check: bound, overflow, canonical range, and
a translation of every byte through `VirtualMapping`. `bootState` instantiates
it for the boot image's subject A:

* address space 1 is owned by subject 1;
* each page of the text range `[textStart, stackStart)` is mapped read-only;
* each page of the stack range `[stackStart, stackTop)` is mapped read/write;
* every mapped page is its own memory object, bound to the frame with the same
  number, so no two pages alias; and
* a stale lifetime retires the stack objects.

`copyPolicy` is the fixed-width, allocation-free form the kernel links. It
reads the layout from the linked symbols and answers with the kernel's result
code. Its agreement with `UserCopy.validate` on `bootState` is checked on the
oracle vectors (`Oracle.userCopyPolicyVectors`, whose expected words are
computed from the model, not from `copyPolicy`) and on a boundary grid
(`copyPolicy_agrees_grid`). That is testing, not a proof for every input.
-/
namespace LeanOS.UserCopyPolicy

open LeanOS LeanOS.VirtualMapping

/-- Result codes, in the order of `boot/kernel.c`'s `enum copy_policy`. -/
def allowed : UInt64 := 0
def tooLong : UInt64 := 1
def overflow : UInt64 := 2
def nonCanonical : UInt64 := 3
def wrongSubject : UInt64 := 4
def unmapped : UInt64 := 5
def readOnly : UInt64 := 6
def stale : UInt64 := 7
/-- Any other rejection; the boot layout never produces one. -/
def other : UInt64 := 8

def pageShift : UInt64 := 12

/-! ## The model instance -/

structure Layout where
  textStart : Nat
  stackStart : Nat
  stackTop : Nat

def Layout.textPage (layout : Layout) (page : Nat) : Bool :=
  layout.textStart / X86PageTable.pageBytes ≤ page &&
    page < layout.stackStart / X86PageTable.pageBytes

def Layout.stackPage (layout : Layout) (page : Nat) : Bool :=
  layout.stackStart / X86PageTable.pageBytes ≤ page &&
    page < (layout.stackTop + X86PageTable.pageBytes - 1) / X86PageTable.pageBytes

def bootState (layout : Layout) (current : Bool) : UserCopy.State where
  virtual :=
    { memory :=
        { capabilities :=
            { subjects := fun subject => subject == 1
              objects := fun _ => true
              kinds := fun _ => some .memory
              slots := fun _ _ => none }
          allocator := { frames := [], status := fun frame => .owned frame }
          binding := fun object =>
            if layout.stackPage object && !current then none else some object
          issued := fun _ => true }
      owner := fun space => if space == 1 then some 1 else none
      mappings := fun space page =>
        if space != 1 then none
        else if layout.textPage page then some { object := page, permissions := { read := true } }
        else if layout.stackPage page then
          some { object := page, permissions := { read := true, write := true } }
        else none
      issuedAddressSpace := fun space => space == 1 }
  userBytes := fun _ _ => 0
  kernelBytes := fun _ _ => 0

def code : Except UserCopy.CopyError (List UserCopy.Location) → UInt64
  | .ok _ => allowed
  | .error .tooLong => tooLong
  | .error .overflow => overflow
  | .error .nonCanonical => nonCanonical
  | .error (.translation .notOwner) => wrongSubject
  | .error (.translation .unmappedPage) => unmapped
  | .error (.translation .missingPermission) => readOnly
  | .error (.translation .retiredObject) => stale
  | .error _ => other

/-- The model's answer for the kernel's arguments. -/
def model (flags start length textStart stackStart stackTop : UInt64) : UInt64 :=
  code (UserCopy.validate
    (bootState { textStart := textStart.toNat, stackStart := stackStart.toNat,
                 stackTop := stackTop.toNat } (flags &&& 2 != 0))
    { caller := (flags >>> 8).toNat, activeAddressSpace := 1 }
    start length.toNat (if flags &&& 1 != 0 then .write else .read))

/-! ## The generated form -/

/-- The code for one byte address: `allowed` or the first failing check, in
`VirtualMapping.translate`'s order (owner, mapping, permission, binding). -/
@[inline] def byteCode (flags address textStart stackStart stackTop : UInt64) : UInt64 :=
  if flags >>> 8 != 1 then wrongSubject
  else
    let page := address >>> pageShift
    if textStart >>> pageShift ≤ page && page < stackStart >>> pageShift then
      if flags &&& 1 != 0 then readOnly else allowed
    else if stackStart >>> pageShift ≤ page && page < (stackTop + 4095) >>> pageShift then
      if flags &&& 2 != 0 then allowed else stale
    else unmapped

/-- One byte of the ascending scan: keep an earlier failure, otherwise check
byte `index` if it is inside the range. -/
@[inline] def scanStep (flags start length textStart stackStart stackTop : UInt64)
    (earlier index : UInt64) : UInt64 :=
  if earlier != allowed then earlier
  else if index < length then byteCode flags (start + index) textStart stackStart stackTop
  else allowed

/-- The first failing byte of `[start, start + length)` for `length ≤ 16`,
unrolled so the generated C is straight-line `uint64_t` code: no recursion
for the entry-stack gate and no `Nat` runtime calls in the boot image. -/
def firstFailure (flags start length textStart stackStart stackTop : UInt64) : UInt64 :=
  let step := scanStep flags start length textStart stackStart stackTop
  step (step (step (step (step (step (step (step (step (step (step (step (step (step
    (step (step allowed 0) 1) 2) 3) 4) 5) 6) 7) 8) 9) 10) 11) 12) 13) 14) 15

/-- `flags` is the access (bit 0: write), the lifetime (bit 1: current) and
the subject (bits 8 and up). Fixed-width and allocation-free. -/
@[export leanos_user_copy_policy]
def copyPolicy (flags start length textStart stackStart stackTop : UInt64) : UInt64 :=
  if length > 16 then tooLong
  else if length = 0 then allowed
  -- The model compares `start + length` with 2^64 and 2^47 as naturals: an
  -- end of exactly 2^64 wraps to 0 here and is non-canonical, not overflow.
  else if start + length < start && start + length != 0 then overflow
  else if start + length == 0 || start + length > 0x800000000000 then nonCanonical
  else firstFailure flags start length textStart stackStart stackTop

/-! ## Agreement on a boundary grid -/

/-- The boot image's linked layout: one text page and two stack pages. -/
def bootText : UInt64 := 0x29a000
def bootStack : UInt64 := 0x29b000
def bootStackTop : UInt64 := 0x29d000

def gridStarts : List UInt64 :=
  [0, 1, 0x299fff, 0x29a000, 0x29afff, 0x29aff8, 0x29b000, 0x29bff8, 0x29cff0,
   0x29cfff, 0x29d000, 0x7ffffffffff8, 0x800000000000, 0xfffffffffffffff8,
   0xffffffffffffffff]
def gridLengths : List UInt64 := [0, 1, 2, 8, 16, 17]
def gridFlags : List UInt64 := [0x100, 0x101, 0x102, 0x103, 0x202, 0x002]

theorem copyPolicy_agrees_grid :
    gridFlags.all (fun flags => gridStarts.all (fun start => gridLengths.all (fun length =>
      copyPolicy flags start length bootText bootStack bootStackTop ==
        model flags start length bootText bootStack bootStackTop))) = true := by
  decide

end LeanOS.UserCopyPolicy
