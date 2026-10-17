import LeanOS.SpawnAllocatorBootRefinement

/-!
# Hosted vectors for the spawn allocator's boot exports (#575)

`lake exe leanos-spawn-allocator` prints the corpus that
`tests/spawn-allocator-host.c` replays against the Lake-generated C of
the `SpawnAllocatorBoot` exports of `LeanOS.SpawnAllocatorWords`.  The expected
words come from the
specification (`specSyscall`, `specStep`: decode, run the allocator, encode),
not from the generated functions, and `syscall_spec`/`kernel_spec` prove the
two agree on every input; the hosted replay checks that the compiled C
agrees too.

The states are many allocator records, not a table: every record reached
from the four family seeds by up to `depth` accepted commands of the
alphabet below (`reachable`), plus records built at the edges of the
representation (`edgeRecords`: counters at their bounds, four children with
large generations and charges, the frame bound) and words that are not
canonical (`malformedWords`).  Every state is paired with every syscall
input and every kernel command of the alphabet.
-/
namespace LeanOS.SpawnAllocatorVectors

open LeanOS
open LeanOS.SpawnAllocator
open LeanOS.SpawnAllocatorWords
open LeanOS.SpawnAllocatorBoot
open LeanOS.CompositeDispatcher (CommandWords)

/-! ## The command alphabet -/

def controlWord (slot generation : UInt64) : UInt64 := (generation <<< 16) ||| slot

def childWords (words : Words) : List UInt64 :=
  [words.child0, words.child1, words.child2, words.child3]

/-- The control words of the live children, then words that name no live
child: a future generation, generation 1 in slot 0, a slot past the table,
and zero. -/
def controls (words : Words) : List UInt64 :=
  let live := ((childWords words).zipIdx).filterMap fun (word, slot) =>
    if word == 0 then none else some (controlWord slot.toUInt64 (word >>> 16))
  live ++ [controlWord 0 words.controlNext, controlWord 0 1, controlWord 5 1, 0]

def input (actor number rbx rcx rdx : UInt64) : SyscallInput := ⟨actor, number, rbx, rcx, rdx⟩

/-- The syscalls tried at a state. -/
def syscallInputs (words : Words) : List SyscallInput :=
  let generation := words.authority
  let spawns :=
    [input 2 100 generation 0x30000 4, input 2 100 generation 0x30000 0x24,
      input 2 100 generation 0x30000 1, input 2 100 (generation + 1) 0x30000 4,
      input 2 100 generation 0x30001 4, input 2 100 generation 0x40000 4,
      input 2 100 generation 0x30000 0x40, input 2 100 0 0x30000 4,
      input 2 100 generation 0x30000 0]
  let grants := (controls words).flatMap fun control =>
    [input 2 101 control 1 0, input 2 101 control 2 0, input 2 101 control 0x10000 0]
  let terminates := (controls words).map fun control => input 2 102 control 0 0
  let memory :=
    [input 2 103 2 0 0, input 2 103 3 0 0, input 2 103 1 0 0, input 2 103 4 0 0,
      input 2 103 2 1 0, input 2 104 2 0 0, input 2 104 3 0 0, input 2 104 0 0 0,
      input 2 104 5 0 0, input 2 104 2 0 1]
  let refusals :=
    [input 1 100 generation 0x30000 4, input 3 104 2 0 0, input 2 99 1 0 0, input 2 105 1 0 0,
      input 2 101 (controlWord 0 1) 0 0, input 2 102 (controlWord 0 1) 1 0]
  spawns ++ grants ++ terminates ++ memory ++ refusals

def command (tag a0 a1 a2 a3 : UInt64) : CommandWords := ⟨tag, a0, a1, a2, a3⟩

/-- The kernel commands tried at a state. -/
def kernelInputs (words : Words) : List CommandWords :=
  [command 0x7501 2 1 0 0, command 0x7501 2 4 0 0, command 0x7501 2 0 0 0,
    command 0x7501 2 5 0 0, command 0x7501 1 1 0 0, command 0x7501 3 1 0 0,
    command 0x7501 2 65 0 0, command 0x7601 2 0 0 0, command 0x7601 1 0 0 0,
    command 0x7601 2 1 0 0, command 0x7701 0 0 0 0] ++
  ((controls words).take 1).map fun control => command 0x7201 control 0 0 0

/-! ## The states -/

/-- The words after a syscall, by the specification. -/
def afterSyscall (words : Words) (given : SyscallInput) : UInt64 × UInt64 × Words :=
  specSyscall words given.actor given.number given.rbx given.rcx given.rdx

/-- The words after a kernel command, by the specification. -/
def afterKernel (words : Words) (given : CommandWords) : UInt64 × UInt64 × Words :=
  let result := specStep words given
  (result.2.1, result.2.2, result.1)

/-- The accepted successors of a state. -/
def successors (words : Words) : List Words :=
  let bySyscall := (syscallInputs words).filterMap fun given =>
    let result := afterSyscall words given
    if result.1 == replyOf 0x01 then some result.2.2 else none
  let byKernel := (kernelInputs words).filterMap fun given =>
    let result := afterKernel words given
    if result.1 == 0x01 then some result.2.2 else none
  bySyscall ++ byKernel

def insertNew (seen : List Words) (candidates : List Words) : List Words × List Words :=
  candidates.foldl (fun (all, fresh) candidate =>
    if all.contains candidate then (all, fresh) else (all ++ [candidate], fresh ++ [candidate]))
    (seen, [])

/-- Breadth-first exploration, `depth` rounds, at most `cap` states. -/
def explore (seen frontier : List Words) (cap : Nat) : Nat → List Words
  | 0 => seen
  | depth + 1 =>
      let (all, fresh) := insertNew seen (frontier.flatMap successors)
      let kept := all.take cap
      let freshKept := fresh.filter kept.contains
      if freshKept.isEmpty then kept else explore kept freshKept cap depth

def seedWordsOf (seed : SpawnBoundary.Seed) : Words := encode (seedRecord seed)

def seeds : List Words :=
  [seedWordsOf .main, seedWordsOf .subjectsExhausted, seedWordsOf .objectsExhausted,
    seedWordsOf .controlsExhausted]

def depth : Nat := 6

def cap : Nat := 160

/-- The records reachable from the seeds. -/
def reachable : List Words := explore seeds seeds cap depth

def maxWord : UInt64 := 0xffffffffffffffff

/-- A child word: generation and charge. -/
def child (generation charge : Nat) : UInt64 := UInt64.ofNat (generation * 65536 + charge)

/-- A frames word: subject budget and the parent's frames. -/
def framesWord (budget parentFrames : Nat) : UInt64 := UInt64.ofNat (budget + parentFrames * 65536)

/-- Records at the edges of the representation. -/
def edgeRecords : List Words :=
  [ -- every counter one below its bound, spawn authority held with budget 4
    ⟨maxWord - 1, maxWord - 1, generationLimit - 1, generationLimit - 1, maxWord - 1,
      maxWord - 2, 0, 0, 0, 0, 5, 0, framesWord 4 1⟩
  , -- four children with large generations and charges, at the frame bound
    ⟨10, 30, 40, 0xfffffffffff0, 9, 8, child 0xffffffffffee 100, child 0xffffffffffef 2000,
      child 7 3, child 1 0, 7, 9, framesWord 4 (0xffff - 2103)⟩
  , -- the parent's memory in both slots, no free frame, budget 4, no children
    ⟨3, 22, 7, 2, 2, 1, 0, 0, 0, 0, 5, 6, framesWord 4 2⟩
  , -- capability identities exhausted
    ⟨3, 21, generationLimit, 1, 2, 1, 0, 0, 0, 0, 0, 0, framesWord 1 3⟩
  , -- control generations exhausted, a child in slot 2
    ⟨4, 22, 8, generationLimit, 2, 1, 0, 0, child 1 1, 0, 0, 0, framesWord 1 3⟩ ]

/-- Words that are not canonical: a zero spawn-generation counter, a child
generation of zero, a generation at the limit, frame bits above bit 32, a
budget above four, and frames that overflow with the charges. -/
def malformedWords : List Words :=
  [ ⟨3, 21, 6, 1, 0, 0, 0, 0, 0, 0, 5, 0, framesWord 0 1⟩
  , ⟨3, 21, 6, 2, 2, 1, 5, 0, 0, 0, 5, 0, framesWord 1 1⟩
  , ⟨3, 21, 6, 2, 2, 1, child (2 ^ 48 - 1) 0, 0, 0, 0, 5, 0, framesWord 1 1⟩
  , ⟨3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, UInt64.ofNat (2 ^ 32)⟩
  , ⟨3, 21, 6, 1, 1, 0, 0, 0, 0, 0, 5, 0, framesWord 5 1⟩
  , ⟨3, 21, 6, 2, 2, 1, child 1 0xffff, 0, 0, 0, 5, 0, framesWord 1 1⟩ ]

def states : List Words := reachable ++ edgeRecords ++ malformedWords

/-! ## The corpus -/

def wordsText (values : List UInt64) : String := ",".intercalate (values.map toString)

/-- One vector: the kind (`s` syscall, `k` kernel), the state words, the
input words, and the expected reply, value and successor words. -/
structure Vector where
  kind : String
  state : Words
  input : List UInt64
  reply : UInt64
  value : UInt64
  next : Words

def syscallVector (words : Words) (given : SyscallInput) : Vector :=
  let result := afterSyscall words given
  ⟨"s", words, [given.actor, given.number, given.rbx, given.rcx, given.rdx], result.1, result.2.1,
    result.2.2⟩

def kernelVector (words : Words) (given : CommandWords) : Vector :=
  let result := afterKernel words given
  ⟨"k", words, [given.tag, given.arg0, given.arg1, given.arg2, given.arg3], result.1, result.2.1,
    result.2.2⟩

def vectors : List Vector :=
  states.flatMap fun words =>
    (syscallInputs words).map (syscallVector words) ++ (kernelInputs words).map (kernelVector words)

def emit : IO Unit := do
  IO.println "leanos-spawn-allocator\t1"
  IO.println s!"expected-seed\t{wordsText (seedWordsOf .main).toList}"
  for entry in vectors.zipIdx do
    let v := entry.1
    IO.println s!"{entry.2}\t{v.kind}\t{wordsText v.state.toList}\t{wordsText v.input}\t{v.reply}\t{v.value}\t{wordsText v.next.toList}"

end LeanOS.SpawnAllocatorVectors
