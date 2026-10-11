import LeanOS.SpawnBoundaryTraces

/-!
# The ring-3 spawn syscall

ADR 0010's 2026-10-10 decision permits a ring-3 spawn syscall for explicit
spawn (#489).  This module is that syscall's decoder and its generated boot
witness.  A subject enters the kernel with `int $0x80`; the number is in RAX
and the arguments in RBX, RCX and RDX.  Five numbers name the five public
commands of the spawn family, with exactly the canonical command words of the
hosted oracles (`SpawnOracle`, `SpawnAccountingOracle`) and of the generated
dispatcher's spawn table (`SpawnBoundary`):

| Number | Command | RBX | RCX | RDX | Command words | Model step |
| --- | --- | --- | --- | --- | --- | --- |
| 100 | spawn | spawn generation | endpoint handle | rights mask | `0x7001 rbx rcx rdx 0` | `childGate (.spawn _)` |
| 101 | grant frames | control word | frames, nonzero | 0 | `0x7101 rbx rcx rdx 0` | `childGate (.grantFrames _ _)` |
| 102 | terminate child | control word | 0 | 0 | `0x7201 rbx rcx rdx 0` | `childGate (.terminateChild _)` |
| 103 | allocate memory | slot | 0 | 0 | `0x7301 rbx rcx rdx 0` | `memoryGate (.allocate _)` |
| 104 | release memory | slot | 0 | 0 | `0x7401 rbx rcx rdx 0` | `memoryGate (.release _)` |

No number reaches the kernel grant or revocation of spawn authority
(`0x7501`, `0x7601`), the timer switch (`0x7701`) or the capability copy
(`0x7801`): those stay commands of the bounded dispatcher only
(`syscall_never_kernel_command`).  No word names the parent, the child's
identity, a frame, or an object identity; the actor is the current subject of
the execution latch.

## The witness

`spawnSyscall state actor number rbx rcx rdx` (export `leanos_spawn_syscall`)
takes the kernel's state token of the spawn family (`SpawnBoundary.StateId`),
the subject that entered the kernel, and the four registers.  In order:

1. a state word that is not a spawn-family token is refused (`0xfe20`);
2. an actor other than the token's current subject is refused (`0xfe21`);
3. a number outside 100..104 is refused (`0xfe22`);
4. registers that are not the canonical encoding of a command are refused
   before any gate runs (`0xfe23`): the words do not decode
   (`canonical_iff_decodes`);
5. otherwise the words go to the boot-compiled dispatcher
   (`CompositeDispatcher.dispatch`).  Its answer is either the reply word of an
   edge of the bounded table, `0x01 | next << 8 | status << 16`, which the
   witness returns, or an error word for a decodable command the bounded table
   does not cover, which the witness turns into `0xfe24`.  The kernel stops
   the machine on `0xfe24`: that command is outside what the table proves.

`spawnSyscallValue` (export `leanos_spawn_syscall_value`) is the hosted
oracle's value word of the same result: the control word of an accepted spawn,
the frames a grant moved or a termination returned, and zero otherwise.

## What is proved

* `spawnSyscall_cases`: every input is one of the five refusals, or exactly one
  edge of `SpawnBoundary.edges` at the presented token, with the same command
  words and the actor the token's current subject.
* `spawnSyscall_refines`: in the edge case, the decoded command is a child or
  memory command (never a kernel command) and the result is exactly one
  `childGate` or `memoryGate` step, with the latch's current subject as the
  actor, on the complete composite state the token names; the successor token
  names the post-state, and the status and value words are the gate's.
* `spawnSyscall_rollback`: on every refusal and every rejected edge, the token
  the kernel keeps names the pre-state itself.
* `spawnSyscall_trace`: every state a syscall reaches satisfies the whole-trace
  theorem `SpawnBoundary.spawn_boundary_trace`.

The witness is a bounded boundary: the spawn table names twenty-one complete
states, and a decodable command at a state the table does not cover is a
fail-stop, not a gate step.
-/
namespace LeanOS.SpawnSyscall

open LeanOS
open LeanOS.FailStop
open LeanOS.SpawnBoundary
open LeanOS.CompositeDispatcher (CommandWords)

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-! ## Numbers and command words -/

def spawnNumber : UInt64 := 100
def grantNumber : UInt64 := 101
def terminateNumber : UInt64 := 102
def allocateNumber : UInt64 := 103
def releaseNumber : UInt64 := 104

/-- The family tag a syscall number names, and `0` for any other number. -/
def syscallTag (number : UInt64) : UInt64 :=
  if number == 100 then 0x7001
  else if number == 101 then 0x7101
  else if number == 102 then 0x7201
  else if number == 103 then 0x7301
  else if number == 104 then 0x7401
  else 0

/-- The command words of a syscall: the number's tag, RBX, RCX, RDX, and a
zero fourth argument. -/
def syscallWords (number rbx rcx rdx : UInt64) : CommandWords :=
  { tag := syscallTag number, arg0 := rbx, arg1 := rcx, arg2 := rdx, arg3 := 0 }

/-- Allocation-free canonical check of the registers for a family tag: the
argument rules of `SpawnOracle.decodeSpawn` and
`SpawnAccountingOracle.decodeChild` and the reserved-zero rule of the memory
commands of `SpawnBoundary.decodeFamily`. -/
def canonical (tag rbx rcx rdx : UInt64) : Bool :=
  if tag == 0x7001 then rbx != 0 && rdx < 64
  else if tag == 0x7101 then rcx != 0 && rdx == 0
  else if tag == 0x7201 || tag == 0x7301 || tag == 0x7401 then rcx == 0 && rdx == 0
  else false

/-- The spawn family's state tokens, `0x7001` to `0x8401`. -/
def familyToken (state : UInt64) : Bool :=
  0x7001 ≤ state && state ≤ 0x8401 && state % 256 == 1

/-- The current subject of the execution latch at a token: subject 1 after the
dispatcher's timer switch (`otherSubject`), and subject 2 everywhere else
(`stateActor_current`). -/
def stateActor (state : UInt64) : UInt64 :=
  if state == 0x7901 then 1 else 2

/-- A reply word of an edge: version 1, a status byte, and nothing above it.
Every error word of the dispatcher has status byte 0. -/
def isEdgeReply (reply : UInt64) : Bool :=
  reply % 256 == 1 && 0x10000 ≤ reply && reply < 0x1000000

/-! ## The generated witness -/

/-- **The spawn syscall's boot witness.**  Allocation-free and fixed-width:
it validates the token, the actor, the number and the canonical registers,
then asks the generated dispatcher.  See the module documentation for the
refusal words. -/
@[export leanos_spawn_syscall]
def spawnSyscall (state actor number rbx rcx rdx : UInt64) : UInt64 :=
  if !familyToken state then 0xfe20
  else if actor != stateActor state then 0xfe21
  else if syscallTag number == 0 then 0xfe22
  else if !canonical (syscallTag number) rbx rcx rdx then 0xfe23
  else
    let reply := CompositeDispatcher.dispatch state (syscallTag number) rbx rcx rdx 0
    if isEdgeReply reply then reply else 0xfe24

/-- The value word of the same result: the hosted oracle's value word of an
accepted edge, and zero for every refusal and rejection. -/
@[export leanos_spawn_syscall_value]
def spawnSyscallValue (state actor number rbx rcx rdx : UInt64) : UInt64 :=
  if isEdgeReply (spawnSyscall state actor number rbx rcx rdx) then
    CompositeDispatcher.dispatchValue state (syscallTag number) rbx rcx rdx 0
  else 0

/-- The refusal words, each returned before any gate runs. -/
def refusals : List UInt64 := [0xfe20, 0xfe21, 0xfe22, 0xfe23, 0xfe24]

/-! ## No syscall reaches a kernel command -/

def syscallTags : List UInt64 := [0x7001, 0x7101, 0x7201, 0x7301, 0x7401]

theorem syscallTag_cases (number : UInt64) :
    syscallTag number = 0 ∨ syscallTag number ∈ syscallTags := by
  unfold syscallTag
  repeat' split
  all_goals simp [syscallTags]

/-- **Kernel commands are not syscalls.**  No syscall number names the kernel
grant or revocation of spawn authority, the timer switch, or the capability
copy. -/
theorem syscall_never_kernel_command (number : UInt64) :
    syscallTag number ≠ grantAuthorityTag ∧ syscallTag number ≠ revokeAuthorityTag ∧
      syscallTag number ≠ switchTag ∧ syscallTag number ≠ copyTag := by
  rcases syscallTag_cases number with zero | member
  · rw [zero]; decide
  · simp only [syscallTags, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h | h | h | h <;> rw [h] <;> decide

/-! ## The canonical check is the decoder -/

/-- A command a syscall may run: a public child command or a memory command. -/
def isSyscallCommand : FamilyCommand → Bool
  | .child (.spawn _) | .child (.grantFrames _ _) | .child (.terminateChild _) => true
  | .memory _ => true
  | _ => false

/-- **The canonical check is exactly decoding.**  For every number and
registers, the check passes exactly when the command words decode, and then
they decode to a syscall command. -/
theorem canonical_iff_decodes (number rbx rcx rdx : UInt64)
    (named : syscallTag number ≠ 0) :
    canonical (syscallTag number) rbx rcx rdx = true ↔
      ∃ command, decodeFamily (syscallWords number rbx rcx rdx) = .ok command ∧
        isSyscallCommand command = true := by
  rcases syscallTag_cases number with zero | member
  · exact absurd zero named
  simp only [syscallTags, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with tag | tag | tag | tag | tag
  · -- spawn
    simp only [canonical, syscallWords, tag, decodeFamily, SpawnAccountingOracle.decodeChild,
      SpawnOracle.decodeSpawn, SpawnOracle.decodeRights, SpawnOracle.spawnCommandTag]
    by_cases zero : rbx = 0
    · subst zero; simp
    · by_cases wide : 64 ≤ rdx
      · have : ¬ rdx < 64 := by
          intro small
          rw [UInt64.le_iff_toNat_le] at wide
          rw [UInt64.lt_iff_toNat_lt] at small
          simp at wide small
          omega
        simp [zero, wide, this]
      · have small : rdx < 64 := by
          rw [UInt64.le_iff_toNat_le] at wide
          rw [UInt64.lt_iff_toNat_lt]
          simp at wide ⊢
          omega
        simp [zero, wide, small, isSyscallCommand]
  · -- grant frames
    simp only [canonical, syscallWords, tag, decodeFamily, SpawnAccountingOracle.decodeChild,
      SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
      SpawnAccountingOracle.terminateChildTag]
    by_cases reserved : rdx = 0
    · subst reserved
      by_cases zero : rcx = 0
      · subst zero; simp
      · simp [zero, isSyscallCommand]
    · simp [reserved]
  · -- terminate child
    simp only [canonical, syscallWords, tag, decodeFamily, SpawnAccountingOracle.decodeChild,
      SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
      SpawnAccountingOracle.terminateChildTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [isSyscallCommand]
      · simp [second]
    · simp [first]
  · -- allocate memory
    simp only [canonical, syscallWords, tag, decodeFamily, SpawnAccountingOracle.decodeChild,
      SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
      SpawnAccountingOracle.terminateChildTag, allocateTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [isSyscallCommand]
      · simp [second]
    · simp [first]
  · -- release memory
    simp only [canonical, syscallWords, tag, decodeFamily, SpawnAccountingOracle.decodeChild,
      SpawnOracle.spawnCommandTag, SpawnAccountingOracle.grantFramesTag,
      SpawnAccountingOracle.terminateChildTag, allocateTag, releaseTag]
    by_cases first : rcx = 0
    · subst first
      by_cases second : rdx = 0
      · subst second
        simp [isSyscallCommand]
      · simp [second]
    · simp [first]

/-! ## Every answer of the spawn table is an edge or an error word -/

/-- The dispatcher's error words (`CompositeDispatcher.errorWord`). -/
def errorWords : List UInt64 := [0xff01, 0xff02, 0xff03, 0xff04, 0xff05, 0xff06]

/-- One scalar row of the generated table: state token, the five command
words, and the reply word. -/
structure Row where
  state : UInt64
  tag : UInt64
  arg0 : UInt64
  arg1 : UInt64
  arg2 : UInt64
  arg3 : UInt64
  reply : UInt64
  deriving DecidableEq, Repr

/-- An edge as the scalar row of the generated table: state token, the five
command words, and the reply word. -/
def edgeRow (edge : Edge) : Row :=
  ⟨encodeState edge.state, edge.words.tag, edge.words.arg0, edge.words.arg1, edge.words.arg2,
    edge.words.arg3, replyWord edge.next edge.status⟩

/-- The 54 rows, as literals. -/
def edgeRows : List Row :=
  [ ⟨28673, 28673, 1, 196608, 4, 0, 8482817⟩, ⟨28673, 28929, 65536, 1, 0, 0, 12808193⟩
  , ⟨28673, 29953, 2, 1, 0, 0, 94465⟩, ⟨28673, 29953, 3, 1, 0, 0, 8417281⟩
  , ⟨28929, 28673, 1, 196608, 4, 0, 94721⟩, ⟨28929, 28673, 2, 196608, 4, 0, 8548609⟩
  , ⟨28929, 28673, 1, 65535, 4, 0, 10514689⟩, ⟨28929, 28673, 1, 262144, 4, 0, 10776833⟩
  , ⟨28929, 28673, 1, 196615, 4, 0, 10711297⟩, ⟨28929, 28673, 1, 262145, 4, 0, 10842369⟩
  , ⟨28929, 28673, 1, 196608, 1, 0, 9072897⟩, ⟨28929, 29185, 65536, 0, 0, 0, 12808449⟩
  , ⟨28929, 30209, 2, 0, 0, 0, 96769⟩, ⟨28929, 29441, 3, 0, 0, 0, 8876289⟩
  , ⟨28929, 30721, 0, 2, 3, 4, 98305⟩, ⟨28929, 30721, 0, 2, 3, 20, 98561⟩
  , ⟨29185, 28673, 1, 196608, 4, 0, 9204225⟩, ⟨29185, 28929, 65536, 1, 0, 0, 12939777⟩
  , ⟨29185, 28929, 131072, 1, 0, 0, 12808705⟩, ⟨29185, 28929, 65535, 1, 0, 0, 12677633⟩
  , ⟨29185, 29697, 2, 0, 0, 0, 94977⟩, ⟨29185, 30465, 0, 0, 0, 0, 96513⟩
  , ⟨29185, 29953, 3, 1, 0, 0, 8417793⟩, ⟨29441, 29697, 2, 0, 0, 0, 9007873⟩
  , ⟨29441, 28929, 65536, 2, 0, 0, 12940033⟩, ⟨29441, 28929, 65536, 1, 0, 0, 95233⟩
  , ⟨29697, 29441, 2, 0, 0, 0, 8877057⟩, ⟨29697, 29185, 65536, 0, 0, 0, 95489⟩
  , ⟨29953, 29185, 65536, 0, 0, 0, 12809473⟩, ⟨29953, 28929, 65536, 1, 0, 0, 12809473⟩
  , ⟨29953, 29441, 2, 0, 0, 0, 95745⟩, ⟨30209, 28673, 1, 196608, 4, 0, 96001⟩
  , ⟨30465, 29185, 65536, 0, 0, 0, 12809985⟩, ⟨30465, 28929, 65536, 1, 0, 0, 12809985⟩
  , ⟨30465, 28673, 1, 196608, 4, 0, 9205505⟩, ⟨30465, 29185, 131072, 0, 0, 0, 96257⟩
  , ⟨30977, 29185, 65536, 0, 0, 0, 12810497⟩, ⟨30977, 28929, 65536, 1, 0, 0, 12810497⟩
  , ⟨30977, 28673, 1, 131073, 4, 0, 8485121⟩, ⟨30977, 29441, 2, 0, 0, 0, 8878337⟩
  , ⟨31233, 28673, 1, 196608, 4, 0, 8485377⟩, ⟨31233, 29953, 2, 1, 0, 0, 97025⟩
  , ⟨31489, 28673, 1, 196608, 4, 0, 8551169⟩, ⟨31489, 28673, 2, 196608, 4, 0, 97281⟩
  , ⟨32001, 28673, 1, 196608, 4, 0, 8617217⟩, ⟨32257, 28673, 1, 196608, 4, 0, 8879617⟩
  , ⟨32513, 28673, 1, 196608, 4, 0, 9273089⟩, ⟨32769, 28673, 1, 393219, 4, 0, 9011201⟩
  , ⟨33025, 28673, 1, 393219, 8, 0, 9142529⟩, ⟨29953, 28673, 1, 196608, 4, 0, 98817⟩
  , ⟨33281, 28929, 131072, 1, 0, 0, 99073⟩, ⟨33281, 28929, 65536, 1, 0, 0, 12812801⟩
  , ⟨33537, 29185, 131072, 0, 0, 0, 99329⟩, ⟨33537, 29185, 65536, 0, 0, 0, 12813057⟩ ]

theorem edgeRows_eq : edges.map edgeRow = edgeRows := by
  decide

private theorem ite_mem {condition : Prop} [Decidable condition] {words : List UInt64}
    {first second : UInt64} (inFirst : first ∈ words) (inSecond : second ∈ words) :
    (if condition then first else second) ∈ words := by
  split
  · exact inFirst
  · exact inSecond

theorem spawnFamilyMiss_mem (tag arg0 arg1 arg2 arg3 : UInt64) :
    CompositeDispatcher.spawnFamilyMiss tag arg0 arg1 arg2 arg3 ∈ errorWords := by
  unfold CompositeDispatcher.spawnFamilyMiss
  repeat' (first | apply ite_mem | decide)

private theorem row_eq {tag arg0 arg1 arg2 arg3 tag' arg0' arg1' arg2' arg3' : UInt64}
    (matched : (tag == tag' && arg0 == arg0' && arg1 == arg1' && arg2 == arg2' &&
      arg3 == arg3') = true) :
    tag = tag' ∧ arg0 = arg0' ∧ arg1 = arg1' ∧ arg2 = arg2' ∧ arg3 = arg3' := by
  simp only [Bool.and_eq_true, beq_iff_eq] at matched
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := matched
  exact ⟨a, b, c, d, e⟩

/-- An answer of the generated spawn table is covered when it is a dispatcher
error word, or the reply word of the row whose state token and command words
are exactly the input. -/
def Covered (state tag arg0 arg1 arg2 arg3 reply : UInt64) : Prop :=
  reply ∈ errorWords ∨ (⟨state, tag, arg0, arg1, arg2, arg3, reply⟩ : Row) ∈ edgeRows

private theorem ite_covered {condition : Prop} [Decidable condition]
    {property : UInt64 → Prop} {first second : UInt64}
    (inFirst : condition → property first) (inSecond : ¬ condition → property second) :
    property (if condition then first else second) := by
  by_cases holds : condition
  · simp only [holds, ↓reduceIte]; exact inFirst holds
  · simp only [holds, ↓reduceIte]; exact inSecond holds

/-- **The generated spawn table, for every input.**  Its answer is a
dispatcher error word, or the reply word of the edge whose state token and
command words are exactly the input. -/
theorem spawnDispatchRaw_cases (state tag arg0 arg1 arg2 arg3 : UInt64) :
    Covered state tag arg0 arg1 arg2 arg3
      (CompositeDispatcher.spawnDispatchRaw state tag arg0 arg1 arg2 arg3) := by
  unfold CompositeDispatcher.spawnDispatchRaw
  have miss := spawnFamilyMiss_mem
  generalize CompositeDispatcher.spawnFamilyMiss = missWord at miss ⊢
  repeat' (apply ite_covered (property := Covered state tag arg0 arg1 arg2 arg3) <;> intro)
  all_goals first
    | (right
       obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := row_eq ‹_›
       subst_vars
       simp [edgeRows]
       done)
    | exact Or.inl (by decide)
    | exact Or.inl (miss _ _ _ _ _)

/-! ## Every syscall is a refusal or one edge -/

private theorem toNat_le {a b : UInt64} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le

theorem dispatch_family (state tag arg0 arg1 arg2 arg3 : UInt64)
    (family : familyToken state = true) :
    CompositeDispatcher.dispatch state tag arg0 arg1 arg2 arg3 =
      CompositeDispatcher.spawnDispatchRaw state tag arg0 arg1 arg2 arg3 := by
  simp only [familyToken, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at family
  obtain ⟨⟨low, high⟩, version⟩ := family
  rw [toNat_le] at low high
  have lowNat : 0x7001 ≤ state.toNat := by simpa using low
  have highNat : state.toNat ≤ 0x8401 := by simpa using high
  unfold CompositeDispatcher.dispatch
  have notInvalidation : (decide (0x1a01 ≤ state) && decide (state ≤ 0x2d01)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, toNat_le]
    right; simp; omega
  have notBudget : (decide (0x4001 ≤ state) && decide (state ≤ 0x4b01)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, toNat_le]
    right; simp; omega
  have notTransfer : (decide (0x5101 ≤ state) && decide (state ≤ 0x5501)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, toNat_le]
    right; simp; omega
  have notRevocation : (decide (0x6001 ≤ state) && decide (state ≤ 0x6501)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, toNat_le]
    right; simp; omega
  have isSpawn : (decide (0x7001 ≤ state) && decide (state ≤ 0x8401)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, toNat_le]
    simp; omega
  simp only [notInvalidation, notBudget, notTransfer, notRevocation, isSpawn,
    Bool.false_eq_true, ↓reduceIte, version, CompositeDispatcher.abiVersion, bne_self_eq_false]

theorem edgeRows_replies : edgeRows.all (fun row => isEdgeReply row.reply) = true := by
  decide

theorem errorWords_not_replies : errorWords.all (fun word => !isEdgeReply word) = true := by
  decide

/-- Membership in the literal rows gives an edge. -/
theorem edge_of_row {row : Row} (member : row ∈ edgeRows) :
    ∃ edge ∈ edges, edgeRow edge = row := by
  rw [← edgeRows_eq] at member
  simpa using member

/-- **Every syscall is a refusal or exactly one edge.**  For every token,
actor, number and registers, the witness either returns one of the five
refusal words, or there is an edge of the bounded table at that token whose
command words are exactly the syscall's, the actor is the token's current
subject, the number names a family command whose registers are canonical, and
the witness returns that edge's reply word. -/
theorem spawnSyscall_cases (state actor number rbx rcx rdx : UInt64) :
    spawnSyscall state actor number rbx rcx rdx ∈ refusals ∨
      ∃ edge ∈ edges, encodeState edge.state = state ∧
        edge.words = syscallWords number rbx rcx rdx ∧
        actor = stateActor state ∧ syscallTag number ≠ 0 ∧
        canonical (syscallTag number) rbx rcx rdx = true ∧
        spawnSyscall state actor number rbx rcx rdx = replyWord edge.next edge.status := by
  unfold spawnSyscall
  by_cases family : familyToken state = true
  · simp only [family, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases sameActor : actor = stateActor state
    · simp only [sameActor, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases named : syscallTag number = 0
      · simp [named, refusals]
      · have namedBeq : (syscallTag number == 0) = false := by simpa using named
        simp only [namedBeq, Bool.false_eq_true, ↓reduceIte]
        by_cases good : canonical (syscallTag number) rbx rcx rdx = true
        · simp only [good, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [dispatch_family _ _ _ _ _ _ family]
          have covered := spawnDispatchRaw_cases state (syscallTag number) rbx rcx rdx 0
          generalize CompositeDispatcher.spawnDispatchRaw state (syscallTag number) rbx rcx rdx 0 =
            reply at covered ⊢
          rcases covered with error | row
          · have notReply := List.all_eq_true.1 errorWords_not_replies _ error
            simp only [Bool.not_eq_true'] at notReply
            simp [notReply, refusals]
          · have isReply := List.all_eq_true.1 edgeRows_replies _ row
            simp only [isReply, ↓reduceIte]
            right
            obtain ⟨edge, member, rowEq⟩ := edge_of_row row
            simp only [edgeRow, Row.mk.injEq] at rowEq
            obtain ⟨stateEq, tagEq, arg0Eq, arg1Eq, arg2Eq, arg3Eq, replyEq⟩ := rowEq
            refine ⟨edge, member, stateEq, ?_, by simp, named, by simp, replyEq.symm⟩
            cases wordsEq : edge.words
            simp only [wordsEq] at tagEq arg0Eq arg1Eq arg2Eq arg3Eq
            simp [syscallWords, tagEq, arg0Eq, arg1Eq, arg2Eq, arg3Eq]
        · simp only [Bool.not_eq_true] at good
          simp [good, refusals]
    · have different : (actor != stateActor state) = true := by simpa using sameActor
      simp [different, refusals]
  · simp only [Bool.not_eq_true] at family
    simp [family, refusals]

/-! ## The edge case refines a gate step -/

/-- Every edge whose tag a syscall can name runs a syscall command. -/
theorem edges_syscall_commands :
    edges.all (fun edge => !syscallTags.contains edge.words.tag || isSyscallCommand edge.command) =
      true := by
  decide

/-- **The current subject at every token.**  `stateActor` is the current
subject of the execution latch on the complete state each token names, by
closed evaluation on the sample boot plan (`native_decide`, classified
`bounded-model`). -/
theorem stateActor_current :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan => allStates.all (fun id =>
          stateActor (encodeState id) == UInt64.ofNat (spawnParent (stateOf plan id)))
      | .error _ => false) = true := by
  native_decide

theorem allStates_complete (id : StateId) : id ∈ allStates := by
  cases id <;> simp [allStates]

theorem stateActor_of_plan (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (id : StateId) :
    stateActor (encodeState id) = UInt64.ofNat (spawnParent (stateOf plan id)) := by
  have holds := stateActor_current
  rw [compiled] at holds
  have one := List.all_eq_true.1 holds id (allStates_complete id)
  simpa using one

/-- The token the kernel keeps after a syscall: the successor token of an edge
reply, and the presented token after a refusal. -/
def nextToken (state reply : UInt64) : UInt64 :=
  if isEdgeReply reply then reply % 0x10000 else state

theorem edges_reply_token :
    edges.all (fun edge => (replyWord edge.next edge.status) % 0x10000 == encodeState edge.next) =
      true := by
  decide


/-- **The syscall path refines the model step.**  When the witness answers
with an edge, the syscall decodes to a public child or memory command (never a
kernel command), the actor is the latch's current subject on the complete
state the token names, and the result is exactly one `childGate` or
`memoryGate` step on that state: its post-state is the state the successor
token names, and its status and value words are the edge's, which are the
witness's reply and value words. -/
theorem spawnSyscall_refines (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (state actor number rbx rcx rdx : UInt64) (edge : Edge) (member : edge ∈ edges)
    (token : encodeState edge.state = state)
    (words : edge.words = syscallWords number rbx rcx rdx)
    (reply : spawnSyscall state actor number rbx rcx rdx = replyWord edge.next edge.status)
    (sameActor : actor = stateActor state) :
    decodeFamily (syscallWords number rbx rcx rdx) = .ok edge.command ∧
      isSyscallCommand edge.command = true ∧
      actor = UInt64.ofNat (spawnParent (stateOf plan edge.state)) ∧
      familyStep (stateOf plan edge.state) edge.command =
        { state := stateOf plan edge.next, status := edge.status, value := edge.value } ∧
      nextToken state (spawnSyscall state actor number rbx rcx rdx) = encodeState edge.next ∧
      spawnSyscallValue state actor number rbx rcx rdx = edge.value := by
  obtain ⟨decoded, dispatched, _, refines⟩ := dispatcher_refines plan compiled edge member
  have isSyscall : isSyscallCommand edge.command = true := by
    have checked := List.all_eq_true.1 edges_syscall_commands edge member
    have tagged : syscallTags.contains edge.words.tag = true := by
      rw [words]
      simp only [syscallWords]
      rcases syscallTag_cases number with zero | inTags
      · -- a zero tag has no edge: every edge's tag is a family tag
        exfalso
        have tagEdge := List.all_eq_true.1 edges_decode edge member
        rw [okIs_iff, words] at tagEdge
        simp [syscallWords, zero, decodeFamily, SpawnAccountingOracle.decodeChild,
          SpawnOracle.decodeSpawn, SpawnOracle.spawnCommandTag,
          SpawnAccountingOracle.grantFramesTag, SpawnAccountingOracle.terminateChildTag,
          allocateTag, releaseTag, grantAuthorityTag, revokeAuthorityTag, switchTag,
          copyTag] at tagEdge
      · simpa using inTags
    simp only [tagged, Bool.not_true, Bool.false_or] at checked
    exact checked
  have isReply : isEdgeReply (replyWord edge.next edge.status) = true :=
    List.all_eq_true.1 edgeRows_replies _ (by rw [← edgeRows_eq]; exact List.mem_map.2 ⟨edge, member, rfl⟩)
  refine ⟨words ▸ decoded, isSyscall, ?_, refines, ?_, ?_⟩
  · rw [sameActor, ← token]
    exact stateActor_of_plan plan compiled edge.state
  · rw [reply]
    simp only [nextToken, isReply, ↓reduceIte]
    have token := List.all_eq_true.1 edges_reply_token edge member
    simpa using token
  · unfold spawnSyscallValue
    rw [reply]
    simp only [isReply, ↓reduceIte]
    have value := dispatched
    simp only [Edge.dispatched, Edge.words] at value
    rw [show encodeFamily edge.command = edge.words from rfl, words, token] at value
    simp only [syscallWords, Prod.mk.injEq] at value
    exact value.2

/-- **Rollback.**  On every refusal the kernel keeps the presented token, and
on every rejected edge the successor token is the presented one and the gate
step returns the pre-state itself.  Either way the complete composite state
the kept token names is the pre-state. -/
theorem spawnSyscall_rollback (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (state actor number rbx rcx rdx : UInt64) :
    spawnSyscall state actor number rbx rcx rdx ∈ refusals ∧
        nextToken state (spawnSyscall state actor number rbx rcx rdx) = state ∨
      ∃ edge ∈ edges, encodeState edge.state = state ∧
        (edge.status = 0x01 ∨
          (nextToken state (spawnSyscall state actor number rbx rcx rdx) = state ∧
            (familyStep (stateOf plan edge.state) edge.command).state =
              stateOf plan edge.state)) := by
  rcases spawnSyscall_cases state actor number rbx rcx rdx with refused | ⟨edge, member, token,
      words, sameActor, _, _, reply⟩
  · left
    refine ⟨refused, ?_⟩
    simp only [refusals, List.mem_cons, List.not_mem_nil, or_false] at refused
    simp only [nextToken]
    rcases refused with h | h | h | h | h <;> rw [h] <;> simp [isEdgeReply]
  · right
    refine ⟨edge, member, token, ?_⟩
    by_cases accepted : edge.status = 0x01
    · exact Or.inl accepted
    · right
      obtain ⟨same, unchanged⟩ := rejected_edge_unchanged plan compiled edge member accepted
      obtain ⟨_, _, _, _, next, _⟩ := spawnSyscall_refines plan compiled state actor number rbx
        rcx rdx edge member token words reply sameActor
      refine ⟨?_, unchanged⟩
      rw [next, same, token]

/-- **The whole-trace theorem holds wherever a syscall leads.**  The complete
state the kernel's token names after any syscall satisfies every conclusion
of `spawn_boundary_trace`. -/
theorem spawnSyscall_trace (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (state actor number rbx rcx rdx : UInt64) (id : StateId) (token : encodeState id = state) :
    ∃ next : StateId,
      nextToken state (spawnSyscall state actor number rbx rcx rdx) = encodeState next ∧
        ResourceRuntimeWellFormed (stateOf plan next) ∧
        ChildAccountingWellFormed (stateOf plan next) ∧
        SpawnTreeWellFormed (stateOf plan next) := by
  rcases spawnSyscall_cases state actor number rbx rcx rdx with refused | ⟨edge, member, edgeToken,
      words, sameActor, _, _, reply⟩
  · refine ⟨id, ?_, ?_⟩
    · simp only [refusals, List.mem_cons, List.not_mem_nil, or_false] at refused
      simp only [nextToken, token]
      rcases refused with h | h | h | h | h <;> rw [h] <;> simp [isEdgeReply]
    · obtain ⟨wf, accounting, tree, _⟩ := spawn_boundary_trace plan id
      exact ⟨wf, accounting, tree⟩
  · obtain ⟨_, _, _, _, next, _⟩ := spawnSyscall_refines plan compiled state actor number rbx rcx
      rdx edge member edgeToken words reply sameActor
    obtain ⟨wf, accounting, tree, _⟩ := spawn_boundary_trace plan edge.next
    exact ⟨edge.next, next, wf, accounting, tree⟩

/-! ## The `spawn-child` image's run (#491)

The image's kernel grants B (subject 2) spawn authority with the bounded
dispatcher's kernel command, then B issues these syscalls.  `image_run` checks
the witness's reply and value words and the token sequence; `image_model`
checks, on the complete states those tokens name, what the transcript reports:
the child table entry, the child's address space, and who holds the frame. -/

/-- One syscall of the image: number, registers, and the expected reply and
value words. -/
structure Call where
  number : UInt64
  rbx : UInt64
  rcx : UInt64
  rdx : UInt64
  reply : UInt64
  value : UInt64
  deriving DecidableEq, Repr

/-- B's syscalls, from the kernel-granted token `authorized`.  Spawn; a
reserved rights bit (refused before any gate); a second spawn over the
subject budget; a grant while B's memory holds the frame; release; grant;
terminate; the stale control word; allocate; spawn into the same child-table
slot (generation 2); the old control word for termination and for a grant,
both rejected; and termination of the new child. -/
def imageCalls : List Call :=
  [ ⟨100, 1, 0x30000, 4, 0x017201, 0x10000⟩
  , ⟨100, 1, 0x30000, 0x40, 0xfe23, 0⟩
  , ⟨100, 1, 0x30000, 4, 0x8c7201, 0⟩
  , ⟨101, 0x10000, 1, 0, 0xc57201, 0⟩
  , ⟨104, 2, 0, 0, 0x017301, 0⟩
  , ⟨101, 0x10000, 1, 0, 0x017401, 1⟩
  , ⟨102, 0x10000, 0, 0, 0x017501, 1⟩
  , ⟨102, 0x10000, 0, 0, 0xc37501, 0⟩
  , ⟨103, 2, 0, 0, 0x017601, 0⟩
  , ⟨100, 1, 0x30000, 4, 0x017701, 0x20000⟩
  , ⟨102, 0x10000, 0, 0, 0xc37701, 0⟩
  , ⟨101, 0x10000, 1, 0, 0xc37701, 0⟩
  , ⟨102, 0x20000, 0, 0, 0x017801, 0⟩ ]

/-- Run the calls from a token as subject 2; `none` on the first mismatch. -/
def runImage (state : UInt64) : List Call → Option (List UInt64)
  | [] => some []
  | call :: rest =>
      let reply := spawnSyscall state 2 call.number call.rbx call.rcx call.rdx
      let value := spawnSyscallValue state 2 call.number call.rbx call.rcx call.rdx
      if reply == call.reply && value == call.value then
        (runImage (nextToken state reply) rest).map (nextToken state reply :: ·)
      else none

/-- **The image's run.**  Every reply and value word is the one the boot
assembly checks, and the tokens are authorized → spawned → spawned → spawned
→ spawned → released → granted → terminated → terminated → reallocated →
respawned → respawned → respawned → secondTerminated. -/
theorem image_run :
    runImage (encodeState .authorized) imageCalls =
      some [encodeState .spawned, encodeState .spawned, encodeState .spawned,
        encodeState .spawned, encodeState .released, encodeState .granted,
        encodeState .terminated, encodeState .terminated, encodeState .reallocated,
        encodeState .respawned, encodeState .respawned, encodeState .respawned,
        encodeState .secondTerminated] := by
  decide

/-- What the transcript reports of a state: B's child-table slot 0, the
recorded address spaces of children 3 and 4, whether they are live, who the
frame is committed to, and the memory object in B's slot 2. -/
def imageView (state : CompositeState) :
    Option ChildEntry × Option Nat × Option Nat × Bool × Bool × Option Nat × Option Nat :=
  (state.spawn.children 2 0, state.spawn.addressSpace 3, state.spawn.addressSpace 4,
    state.capabilities.subjects 3, state.capabilities.subjects 4,
    state.frameBudgets.commitment 4, (state.capabilities.slots 2 2).map (·.object))

/-- **The model behind the transcript** (`native_decide`, classified
`bounded-model`): child 3 with address space 21 under generation 1; the frame
committed to it by the grant and back to B on termination; B's memory object
20 released and object 22 allocated; child 4 with address space 23 in the same
slot under generation 2; nothing live at the end. -/
theorem image_model :
    (match BootPageTablePlan.compile BootPageTablePlan.sampleInput with
      | .ok plan =>
          imageView (stateOf plan .spawned) ==
              (some ⟨3, 1, 0⟩, some 21, none, true, false, some 2, some 20) &&
            imageView (stateOf plan .released) ==
              (some ⟨3, 1, 0⟩, some 21, none, true, false, some 2, none) &&
            imageView (stateOf plan .granted) ==
              (some ⟨3, 1, 1⟩, some 21, none, true, false, some 3, none) &&
            imageView (stateOf plan .terminated) ==
              (none, none, none, false, false, some 2, none) &&
            imageView (stateOf plan .reallocated) ==
              (none, none, none, false, false, some 2, some 22) &&
            imageView (stateOf plan .respawned) ==
              (some ⟨4, 2, 0⟩, none, some 23, false, true, some 2, some 22) &&
            imageView (stateOf plan .secondTerminated) ==
              (none, none, none, false, false, some 2, some 22)
      | .error _ => false) = true := by
  native_decide

end LeanOS.SpawnSyscall
