import LeanOS.Refinement.ChildLoaderC
import LeanOS.Refinement.NetworkSubjectC
import LeanOS.Refinement.DhcpSubjectC
import LeanOS.Refinement.SpawnAllocatorC

/-!
# Negative fixtures for the #570 and #593 refinement theorems

Each rung-3 theorem of issues #570 and #593 states that a checked-in C AST
computes a Lean witness. These fixtures show the statements have teeth on both sides:

* **a mutated export (C side):** the emitted AST with one constant or one
  comparison changed computes a different answer on a concrete input, so the
  refinement theorem cannot hold of it (the build's drift check also rejects
  such C; `scripts/check-refinement-mutants.sh`);
* **a mutated export (Lean side):** the unchanged emitted AST disagrees with
  a mutated Lean witness on a concrete input, so the theorem cannot be
  restated about it.

Weakened claim statements are rejected by the pinned contract
`tests/RefinementStatements.lean` (`claim` rows of
`tests/fixtures/refinement-mutants.tsv`).
-/
namespace LeanOS.NegativeFixtures.ExportRefinement

open LeanOS LeanOS.Refinement.CSubset

/-! ## Mutating an AST -/

mutual
/-- Rewrite one literal assignment of a statement list with `f`: `some n`
skips `n` more literals in source order, `none` means the rewrite is done. -/
def mutateList (f : UInt64 → UInt64) : Option Nat → List Stmt → Option Nat × List Stmt
  | n, [] => (n, [])
  | n, stmt :: rest =>
      let (n', stmt') := mutateStmt f n stmt
      let (n'', rest') := mutateList f n' rest
      (n'', stmt' :: rest')

def mutateStmt (f : UInt64 → UInt64) : Option Nat → Stmt → Option Nat × Stmt
  | some 0, .assign name (.lit v) => (none, .assign name (.lit (f v)))
  | some (n + 1), .assign name (.lit v) => (some n, .assign name (.lit v))
  | n, .ifZero name t e =>
      let (n', t') := mutateList f n t
      let (n'', e') := mutateList f n' e
      (n'', .ifZero name t' e')
  | n, .block label body =>
      let (n', body') := mutateList f n body
      (n', .block label body')
  | n, stmt => (n, stmt)
end

/-- `func` with its `n`-th literal assignment rewritten by `f`. -/
def mutateLiteral (func : Func) (n : Nat) (f : UInt64 → UInt64) : Func :=
  { func with body := (mutateList f (some n) func.body).2 }

/-! ## `leanos_loader_source` -/

open LeanOS.ChildLoader LeanOS.Refinement.ChildLoaderC

/-- The emitted check with its first literal, the placement refusal `6`,
changed to `7`. -/
def loaderSourceMutantC : Func := mutateLiteral loaderSourceC 0 fun _ => 7

/- A source inside the authority at the wrong offset: the mutant answers 7. -/
/--
error: Tactic `decide` proved that the proposition
  call loaderSourceMutantC [5, 0, 100, 4, 10] = some (loaderSource 5 0 100 4 10)
is false
-/
#guard_msgs in
example : call loaderSourceMutantC [5, 0, 100, 4, 10] = some (loaderSource 5 0 100 4 10) := by
  decide

/-- The emitted check agrees on the same input. -/
example : call loaderSourceC [5, 0, 100, 4, 10] = some (loaderSource 5 0 100 4 10) := by
  decide

/-- A Lean witness that forgets the read authority's upper bound. -/
def unboundedLoaderSource (source start _stop fileOffset _span : UInt64) : UInt64 :=
  if source < start then 5
  else if source != start + fileOffset then 6
  else 0

/- A segment that runs past the authority: the emitted C refuses it, the
mutated witness accepts it, so the C does not refine the mutated witness. -/
/--
error: Tactic `decide` proved that the proposition
  call loaderSourceC [5, 0, 10, 5, 10] = some (unboundedLoaderSource 5 0 10 5 10)
is false
-/
#guard_msgs in
example : call loaderSourceC [5, 0, 10, 5, 10] = some (unboundedLoaderSource 5 0 10 5 10) := by
  decide

/-! ## `leanos_loader_decide` -/

/-- The emitted decision with its unknown-request answer `511` changed. -/
def loaderDecideMutantC : Func := mutateLiteral loaderDecideC 2 fun _ => 3

/--
error: Tactic `decide` proved that the proposition
  call loaderDecideMutantC [9, 0, 0, 0, 0, 0] = some (loaderDecide 9 0 0 0 0 0)
is false
-/
#guard_msgs in
example : call loaderDecideMutantC [9, 0, 0, 0, 0, 0] = some (loaderDecide 9 0 0 0 0 0) := by
  decide

/-- A Lean decision that drops the frame test of a writable load. -/
def framelessLoaderDecide (op flags sourceCode pages frames used : UInt64) : UInt64 :=
  if op == 1 && flags == 0x55 then 2 else loaderDecide op flags sourceCode pages frames used

/- A writable, unloaded, named segment of the live child with no frames to
spare: the emitted C refuses it (`0x208`). -/
/--
error: Tactic `decide` proved that the proposition
  call loaderDecideC [1, 85, 0, 1, 0, 0] = some (framelessLoaderDecide 1 85 0 1 0 0)
is false
-/
#guard_msgs in
example : call loaderDecideC [1, 0x55, 0, 1, 0, 0] =
    some (framelessLoaderDecide 1 0x55 0 1 0 0) := by
  decide

/-! ## `leanos_frame_copy_check` -/

open LeanOS.NetworkSubject LeanOS.Refinement.NetworkSubjectC in
/-- The emitted helper with its holder (`3`, the network subject) changed. -/
def frameCopyDecideMutantC : Func := mutateLiteral frameCopyDecideC 0 fun _ => 4

open LeanOS.NetworkSubject LeanOS.Refinement.NetworkSubjectC in
/- The holder asks an unknown operation: the mutant refuses it as a
non-holder (1) instead of answering 5. -/
/--
error: Tactic `decide` proved that the proposition
  callWith (noCalls.add "l_LeanOS_NetworkSubject_frameCopyDecide" frameCopyDecideMutantC) frameCopyCheckC
      [3, 0, 0, 0, 0, 0] =
    some (frameCopyCheck 3 0 0 0 0 0)
is false
-/
#guard_msgs in
example : callWith (noCalls.add "l_LeanOS_NetworkSubject_frameCopyDecide" frameCopyDecideMutantC)
    frameCopyCheckC [3, 0, 0, 0, 0, 0] = some (frameCopyCheck 3 0 0 0 0 0) := by
  decide

open LeanOS.NetworkSubject in
/-- A Lean witness that ignores the slot's pending flag. -/
def pendinglessFrameCopyCheck (subject request addr len base limit : UInt64) : UInt64 :=
  frameCopyCheck subject (request &&& 0xff) addr len base limit

open LeanOS.NetworkSubject LeanOS.Refinement.NetworkSubjectC in
/- A fetch with a frame pending: the emitted C accepts it (0), the mutated
witness reports no frame (2). -/
/--
error: Tactic `decide` proved that the proposition
  callWith (link noCalls) frameCopyCheckC [3, 257, 0, 100, 0, 1000] =
    some (pendinglessFrameCopyCheck 3 257 0 100 0 1000)
is false
-/
#guard_msgs in
example : callWith (link noCalls) frameCopyCheckC [3, 0x101, 0, 100, 0, 1000] =
    some (pendinglessFrameCopyCheck 3 0x101 0 100 0 1000) := by
  decide

/-! ## `leanos_frame_port_check` -/

open LeanOS.DhcpSubject LeanOS.Refinement.DhcpSubjectC in
/-- The emitted check with its first port holder (`2`, the DHCP subject)
changed. -/
def framePortCheckMutantC : Func := mutateLiteral framePortCheckC 4 fun _ => 4

/-- A fetch request of the DHCP subject for its own window with a frame
pending: operation 1, pending 1, route 2, owner 2. -/
def dhcpFetch : UInt64 := 0x02020101

open LeanOS.DhcpSubject LeanOS.Refinement.DhcpSubjectC in
/--
error: Tactic `decide` proved that the proposition
  call framePortCheckMutantC [2, dhcpFetch, 0, 100, 0, 1000] = some (framePortCheck 2 dhcpFetch 0 100 0 1000)
is false
-/
#guard_msgs in
example : call framePortCheckMutantC [2, dhcpFetch, 0, 100, 0, 1000] =
    some (framePortCheck 2 dhcpFetch 0 100 0 1000) := by
  decide

open LeanOS.DhcpSubject in
/-- A Lean witness that takes the window's owner to be the caller. -/
def ownerlessFramePortCheck (subject req addr len base limit : UInt64) : UInt64 :=
  framePortCheck subject ((req &&& (0xffffff : UInt64)) ||| ((subject &&& (0xff : UInt64)) <<< (24 : UInt64)))
    addr len base limit

open LeanOS.DhcpSubject LeanOS.Refinement.DhcpSubjectC in
/- The DHCP subject passing the echo subject's window (owner 3): the emitted
C refuses it (2), the mutated witness accepts it. -/
/--
error: Tactic `decide` proved that the proposition
  call framePortCheckC [2, 50462977, 0, 100, 0, 1000] = some (ownerlessFramePortCheck 2 50462977 0 100 0 1000)
is false
-/
#guard_msgs in
example : call framePortCheckC [2, 0x03020101, 0, 100, 0, 1000] =
    some (ownerlessFramePortCheck 2 0x03020101 0 100 0 1000) := by
  decide

/-! ## The spawn allocator's exports (#593)

The ASTs run linked with the emitted helpers (`SpawnAllocatorC.link`). The
inputs are the family seed's words: subjects up to 2 issued, the parent's
spawn authority not yet granted, memory object 20 in slot 2, one frame
committed to the parent. -/

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/-- The emitted seed export with its first word (subjects issued, `3`)
changed. -/
def seedMutantC : Func := mutateLiteral seedC 0 fun _ => 4

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/--
error: Tactic `decide` proved that the proposition
  callWith (link noCalls) seedMutantC [0] = some (seed 0)
is false
-/
#guard_msgs in
example : callWith (link noCalls) seedMutantC [0] = some (seed 0) := by
  decide

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/-- The emitted seed export agrees on the same word. -/
example : callWith (link noCalls) seedC [0] = some (seed 0) := by
  decide

open LeanOS.SpawnAllocatorWords LeanOS.Refinement.SpawnAllocatorC in
/-- The emitted decision helper with its spawn tag (`0x7001`) changed. -/
def decideMutantC : Func := mutateLiteral decideWC 0 fun _ => 0x7002

open LeanOS.SpawnAllocatorWords LeanOS.Refinement.SpawnAllocatorC in
/- A spawn before the kernel grants spawn authority: the model rejects it
(`0x81`); the mutant no longer knows the tag and accepts it (`0x01`). -/
/--
error: Tactic `decide` proved that the proposition
  callWith (link noCalls) decideMutantC [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 65536, 28673, 1, 0, 0] =
    some (decideW 3 21 6 1 1 0 0 0 0 0 5 0 65536 28673 1 0 0)
is false
-/
#guard_msgs in
example : callWith (link noCalls) decideMutantC
    [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0x10000, 0x7001, 1, 0, 0] =
    some (decideW 3 21 6 1 1 0 0 0 0 0 5 0 0x10000 0x7001 1 0 0) := by
  decide

open LeanOS.SpawnAllocatorWords LeanOS.Refinement.SpawnAllocatorC in
/-- The emitted decision agrees on the same input. -/
example : callWith (link noCalls) decideWC
    [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0x10000, 0x7001, 1, 0, 0] =
    some (decideW 3 21 6 1 1 0 0 0 0 0 5 0 0x10000 0x7001 1 0 0) := by
  decide

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/-- The emitted syscall export with the "no refusal" word it compares the
refusal against (`0`) changed. -/
def syscallMutantC : Func := mutateLiteral syscallC 0 fun _ => 1

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/- The parent allocates memory into slot 3: no refusal applies, and the
mutant returns the refusal word `0` instead of the allocator's reply. -/
/--
error: Tactic `decide` proved that the proposition
  callWith (link noCalls) syscallMutantC [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 65536, 2, 103, 3, 0, 0] =
    some (syscall 3 21 6 1 1 0 0 0 0 0 5 0 65536 2 103 3 0 0)
is false
-/
#guard_msgs in
example : callWith (link noCalls) syscallMutantC
    [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0x10000, 2, 103, 3, 0, 0] =
    some (syscall 3 21 6 1 1 0 0 0 0 0 5 0 0x10000 2 103 3 0 0) := by
  decide

open LeanOS.SpawnAllocatorBoot in
/-- A Lean syscall that forgets the parent-only rule. -/
def actorlessSyscall (w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f _actor number rbx rcx rdx : UInt64) :
    UInt64 :=
  syscall w0 w1 w2 w3 w4 w5 c0 c1 c2 c3 m2 m3 f 2 number rbx rcx rdx

open LeanOS.SpawnAllocatorBoot LeanOS.Refinement.SpawnAllocatorC in
/- Subject 3 asks for the same allocation: the emitted C refuses it
(`0xfe21`), the mutated witness allocates. -/
/--
error: Tactic `decide` proved that the proposition
  callWith (link noCalls) syscallC [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 65536, 3, 103, 3, 0, 0] =
    some (actorlessSyscall 3 21 6 1 1 0 0 0 0 0 5 0 65536 3 103 3 0 0)
is false
-/
#guard_msgs in
example : callWith (link noCalls) syscallC
    [3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, 0x10000, 3, 103, 3, 0, 0] =
    some (actorlessSyscall 3 21 6 1 1 0 0 0 0 0 5 0 0x10000 3 103 3 0 0) := by
  decide

end LeanOS.NegativeFixtures.ExportRefinement
