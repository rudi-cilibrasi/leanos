/-!
# The SMAP copy window as a checked instruction plan (issue #478)

`smap_copy_from` and `smap_copy_to` in `boot/boot.S` are the only kernel code
that opens the AC window (`stac`) to touch user memory. This module defines
each window as data: an exact instruction list, its encoding, and the labels
the image policy and entry checks refer to. `scripts/check-smap-window.py`
confirms that the bytes at those symbols in every final ELF equal the plan's
encoding, so an edit to the assembly that is not also made here fails the
build.

The proofs are over the plan as data. A small abstract machine tracks one bit,
whether the window opened by `stac` is still open, and records every way the
plan can leave: a `ret`, or a fault raised by the copy instruction. The
theorems say that every `ret` and `popfq` happens with the window closed, that
user memory is touched only while it is open, and that the copy is the only
instruction that can fault.

What this does not prove:

* **No x86 semantics.** The meaning of each instruction (that `stac` sets AC,
  `clac` clears it, `popfq` restores the flags `pushfq` saved, and that only
  `rep movsb` touches memory) is read from the x86 manual. The CPU still
  executes unverified machine code; the check is byte equality with this plan.
* **The fault exit is not closed here.** A page fault inside `rep movsb` leaves
  with AC still set. The interrupt entry stubs clear AC and DF on every vector
  (`ENTRY-POLICY ... cleanup=AC,DF`, checked on the final ELF); that check, not
  this module, closes the fault exit.
* **Callers.** `popfq` restores the caller's AC, which is clear because AC is
  set nowhere else in the kernel (`check-image-policy.sh` counts every `stac`).
-/
namespace LeanOS.SmapWindowPlan

/-- The instructions a window may use. -/
inductive Instr where
  | pushfq
  | cli
  | cld
  | stac
  | movRdxRcx
  | repMovsb
  | clac
  | popfq
  | ret
  deriving DecidableEq, Repr

/-- The encodings `boot.S` assembles to, identical under GNU as and Clang's
integrated assembler. -/
def Instr.bytes : Instr → List UInt8
  | .pushfq => [0x9c]
  | .cli => [0xfa]
  | .cld => [0xfc]
  | .stac => [0x0f, 0x01, 0xcb]
  | .movRdxRcx => [0x48, 0x89, 0xd1]
  | .repMovsb => [0xf3, 0xa4]
  | .clac => [0x0f, 0x01, 0xca]
  | .popfq => [0x9d]
  | .ret => [0xc3]

/-- Both windows have the same body: save flags, mask interrupts, clear DF,
open AC, copy `rdx` bytes from `rsi` to `rdi`, close AC, restore flags. -/
def copyBody : List Instr :=
  [.pushfq, .cli, .cld, .stac, .movRdxRcx, .repMovsb, .clac, .popfq, .ret]

structure Window where
  symbol : String
  body : List Instr
  /-- Internal labels as (symbol, instruction index). -/
  labels : List (String × Nat)

def window (name : String) : Window :=
  { symbol := name, body := copyBody
    labels := [(name ++ "_cld", 2), (name ++ "_stac", 3), (name ++ "_clac", 6)] }

def windows : List Window := [window "smap_copy_from", window "smap_copy_to"]

def encode (body : List Instr) : List UInt8 := body.flatMap Instr.bytes

/-- Byte offset of instruction `index` within `body`. -/
def offsetOf (body : List Instr) (index : Nat) : Nat := (encode (body.take index)).length

/-! ## The AC-window machine -/

inductive Exit where
  /-- A `ret`, with whether the window was still open. -/
  | ret (windowOpen : Bool)
  /-- A fault raised by instruction `index`, with whether the window was open. -/
  | fault (index : Nat) (windowOpen : Bool)
  deriving DecidableEq, Repr

/-- Only the copy instruction touches memory, so only it can fault. -/
def Instr.mayFault : Instr → Bool
  | .repMovsb => true
  | _ => false

/-- Only the copy instruction accesses user memory. -/
def Instr.touchesUser : Instr → Bool
  | .repMovsb => true
  | _ => false

structure Trace where
  exits : List Exit
  /-- Instructions that touched user memory, with the window bit at the time. -/
  userAccesses : List (Nat × Bool)
  /-- `popfq` executions, with the window bit at the time. -/
  flagRestores : List Bool
  deriving DecidableEq, Repr

/-- Run the straight-line body from `index`, tracking only the window bit. -/
def run : List Instr → Nat → Bool → Trace
  | [], _, _ => { exits := [], userAccesses := [], flagRestores := [] }
  | instr :: rest, index, windowOpen =>
    let next := match instr with
      | .stac => true
      | .clac => false
      | _ => windowOpen
    let tail := if instr = .ret then { exits := [], userAccesses := [], flagRestores := [] }
      else run rest (index + 1) next
    { exits := (if instr.mayFault then [.fault index windowOpen] else []) ++
        (if instr = .ret then [.ret windowOpen] else []) ++ tail.exits
      userAccesses := (if instr.touchesUser then [(index, windowOpen)] else []) ++
        tail.userAccesses
      flagRestores := (if instr = .popfq then [windowOpen] else []) ++ tail.flagRestores }

def trace (body : List Instr) : Trace := run body 0 false

/-- The property the build relies on: every `ret` and every flag restore
happens with the window closed, every user access happens with it open, a
`ret` exists, and only user accesses can fault. -/
def acSafe (body : List Instr) : Bool :=
  let t := trace body
  t.exits.any (fun e => match e with | .ret _ => true | _ => false) &&
    t.exits.all (fun e => match e with
      | .ret windowOpen => !windowOpen
      | .fault index _ => t.userAccesses.any (·.1 == index)) &&
    t.userAccesses.all (·.2) &&
    t.flagRestores.all (! ·)

theorem copyBody_acSafe : acSafe copyBody = true := by decide

theorem windows_acSafe : ∀ w ∈ windows, acSafe w.body = true := by decide

/-- Every `ret` in either window leaves with the window closed. -/
theorem windows_ret_closed :
    ∀ w ∈ windows, ∀ windowOpen, Exit.ret windowOpen ∈ (trace w.body).exits →
      windowOpen = false := by decide

/-- User memory is touched only with the window open. -/
theorem windows_access_inside :
    ∀ w ∈ windows, ∀ access ∈ (trace w.body).userAccesses, access.2 = true := by decide

/-- The only fault exit is the copy instruction, and it leaves with the window
open: this is the exit the interrupt entry's AC cleanup must close. -/
theorem windows_fault_exit :
    ∀ w ∈ windows, (trace w.body).exits.filter (fun e => match e with
      | .fault _ _ => true | _ => false) = [.fault 5 true] := by decide

theorem copyBody_encoding :
    encode copyBody =
      [0x9c, 0xfa, 0xfc, 0x0f, 0x01, 0xcb, 0x48, 0x89, 0xd1, 0xf3, 0xa4,
       0x0f, 0x01, 0xca, 0x9d, 0xc3] := by decide

theorem copyBody_label_offsets :
    offsetOf copyBody 2 = 2 ∧ offsetOf copyBody 3 = 3 ∧ offsetOf copyBody 6 = 11 := by
  decide

private def hex (byte : UInt8) : String :=
  let digits := Nat.toDigits 16 byte.toNat
  String.ofList (if digits.length < 2 then '0' :: digits else digits)

/-- Rendered for `scripts/check-smap-window.py`: one `window` row with the
exact bytes, then one `label` row per internal label with its byte offset. -/
def emit : IO Unit := do
  IO.println "leanos-smap-window-plan\t1"
  for w in windows do
    IO.println s!"window\t{w.symbol}\t{" ".intercalate ((encode w.body).map hex)}"
    for (label, index) in w.labels do
      IO.println s!"label\t{label}\t{w.symbol}\t{offsetOf w.body index}"

end LeanOS.SmapWindowPlan
