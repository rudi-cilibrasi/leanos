import LeanOS.Oracle.Composite
import LeanOS.ChildLoader

/-!
# Oracle corpus: the run-time loader

The run-time loader's rows, with their expected-word and model checks.  The
spawn family's own rows left this corpus with the fixed spawn table (#575):
its boot exports take thirteen state words, and the hosted spawn-allocator
corpus (`LeanOS.SpawnAllocatorVectors`) replays them.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

private def loaderSource (id : String) (source start stop fileOffset span : UInt64) : Vector :=
  { id, adapter := "ChildLoader.source", words := [source, start, stop, fileOffset, span],
    expected := ChildLoader.loaderSource source start stop fileOffset span }

private def loaderDecide (id : String) (op flags sourceCode pages frames used : UInt64) :
    Vector :=
  { id, adapter := "ChildLoader.decide", words := [op, flags, sourceCode, pages, frames, used],
    expected := ChildLoader.loaderDecide op flags sourceCode pages frames used }

/-- The run-time loader's witnesses (#492), on a reserved range of four
pages at `0x400000` holding a text segment at file offset `0x1000` and a data
segment at `0x2000`, one page each: the source check inside, below, past and
across the end of the range, at the wrong placement, and with a span larger
than the range; then every decision: in place, by copy, the two refusals
without effect, every rollback, a started child, an incomplete start, an
unknown request, and maximum words. -/
def loaderVectors : List Vector := [
  loaderSource "loader-source.text-in-place" 0x401000 0x400000 0x404000 0x1000 0x1000,
  loaderSource "loader-source.data-copy" 0x402000 0x400000 0x404000 0x2000 0x1000,
  loaderSource "loader-source.below-range" 0x3ff000 0x400000 0x404000 0x1000 0x1000,
  loaderSource "loader-source.past-range" 0x404000 0x400000 0x404000 0x1000 0x1000,
  loaderSource "loader-source.across-end" 0x403800 0x400000 0x404000 0x1000 0x1000,
  loaderSource "loader-source.wrong-placement" 0x402000 0x400000 0x404000 0x1000 0x1000,
  loaderSource "loader-source.span-beyond-range" 0x401000 0x400000 0x800 0 0x1000,
  loaderSource "loader-source.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff,
  loaderDecide "loader-decide.load-in-place" 1 5 0 1 1 0,
  loaderDecide "loader-decide.load-copy" 1 21 0 1 1 0,
  loaderDecide "loader-decide.refused-no-child" 1 0 0 1 1 0,
  loaderDecide "loader-decide.refused-started" 1 2 0 1 1 0,
  loaderDecide "loader-decide.rollback-bad-index" 1 1 0 0 1 0,
  loaderDecide "loader-decide.rollback-already-loaded" 1 13 0 1 1 0,
  loaderDecide "loader-decide.rollback-outside-authority" 1 5 5 1 1 0,
  loaderDecide "loader-decide.rollback-wrong-source" 1 5 6 1 1 0,
  loaderDecide "loader-decide.rollback-in-place-zero-fill" 1 37 0 1 1 0,
  loaderDecide "loader-decide.rollback-no-frames" 1 21 0 1 0 0,
  loaderDecide "loader-decide.rollback-frames-used" 1 21 0 1 1 1,
  loaderDecide "loader-decide.start" 2 65 0 0 0 0,
  loaderDecide "loader-decide.rollback-incomplete" 2 1 0 0 0 0,
  loaderDecide "loader-decide.start-refused-no-child" 2 64 0 0 0 0,
  loaderDecide "loader-decide.unknown-request" 3 65 0 0 0 0,
  loaderDecide "loader-decide.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff]

/-- The loader corpus's expected words. -/
theorem loader_vectors_expected :
    loaderVectors.map (·.expected) =
      [0, 0, 5, 5, 5, 6, 5, 5,
        1, 2, 0x101, 0x102, 0x203, 0x204, 0x205, 0x206, 0x207, 0x208, 0x208, 3, 0x209, 0x101,
        0x1ff, 0x1ff] := by
  decide

/-! ## The loader along the `spawn-loader` scenario (#571)

The loader model's states along the scenario's requests, on a four-page
reserved range at `0x400000` holding an admitted file with a text segment (one
page at `0x1000000`, read-execute, file offset `0x1000`) and a data segment
(one page at `0x1001000`, read-write, file offset `0x2000`, eight file bytes
and a zero-filled tail).  The file's byte at offset `i` is `i % 251`.  The
requests are the image's: a load claiming a source one page below the range
(rolled back), the same load with the old control word (refused), after the
respawn the text segment in place and the data segment by copy, the start,
and then a load and a start after the start (refused).  Each vector carries
the words the kernel computes from the model state (`flagsWord`, the source
witness's answer, the segment's pages, the child's frames, the frames used),
so its expected word is the generated decision for that state. -/

/-- The scenario's admitted plan. -/
def loaderTracePlan : List ElfAdmission.Segment :=
  [{ vaddr := 0x1000000, memBytes := 0x100, fileOffset := 0x1000, fileBytes := 0x100,
     readable := true, writable := false, executable := true },
   { vaddr := 0x1001000, memBytes := 0x900, fileOffset := 0x2000, fileBytes := 0x8,
     readable := true, writable := true, executable := false }]

/-- The loader with no child, before the first spawn. -/
def loaderTraceIdle : ChildLoader.State :=
  { start := 0x400000, stop := 0x404000, plan := loaderTracePlan, child := none,
    loaded := fun _ => false, leaves := fun _ => none, used := 0, started := false,
    file := fun offset => UInt8.ofNat (offset % 251), frameBytes := fun _ _ => 0 }

/-- The first child, with the frame its parent gave it. -/
def loaderTraceFirst : ChildLoader.State :=
  { loaderTraceIdle with child := some ⟨0x10000, 1⟩ }

def loaderTraceRejected : ChildLoader.Request := .load 0x10000 0 0x3ff000

/-- The loader after the rollback. -/
def loaderTraceRolledBack : ChildLoader.State :=
  (ChildLoader.step loaderTraceFirst loaderTraceRejected).1

/-- The respawned child, with the frame its parent gave it. -/
def loaderTraceSecond : ChildLoader.State :=
  { loaderTraceRolledBack with child := some ⟨0x20000, 1⟩ }

def loaderTraceText : ChildLoader.State :=
  (ChildLoader.step loaderTraceSecond (.load 0x20000 0 0x401000)).1

def loaderTraceData : ChildLoader.State :=
  (ChildLoader.step loaderTraceText (.load 0x20000 1 0x402000)).1

def loaderTraceStarted : ChildLoader.State :=
  (ChildLoader.step loaderTraceData (.start 0x20000)).1

/-- The scenario's requests, each with the loader state it runs in. -/
def loaderTraceSteps : List (ChildLoader.State × ChildLoader.Request) :=
  [(loaderTraceFirst, loaderTraceRejected),
   (loaderTraceRolledBack, .load 0x10000 0 0x401000),
   (loaderTraceSecond, .load 0x20000 0 0x401000),
   (loaderTraceText, .load 0x20000 1 0x402000),
   (loaderTraceData, .start 0x20000),
   (loaderTraceStarted, .load 0x20000 1 0x402000),
   (loaderTraceStarted, .start 0x10000)]

/-- The decision witness's words for a request in a model state, as
`loader_witness_agrees_load` and `loader_witness_agrees_start` compute them. -/
def loaderTraceVector (id : String) (state : ChildLoader.State) :
    ChildLoader.Request → Vector
  | .load control index source =>
      let sourceCode := match state.plan[index]? with
        | some segment => ChildLoader.loaderSource (UInt64.ofNat source)
            (UInt64.ofNat state.start) (UInt64.ofNat state.stop)
            (UInt64.ofNat segment.fileOffset)
            (UInt64.ofNat (ChildLoader.pageCount segment * ElfAdmission.pageBytes))
        | none => 0
      loaderDecide id 1 (ChildLoader.flagsWord state (.load control index source)) sourceCode
        (UInt64.ofNat ((state.plan[index]?.map ChildLoader.pageCount).getD 0))
        (UInt64.ofNat ((state.child.map (·.frames)).getD 0)) (UInt64.ofNat state.used)
  | .start control => loaderDecide id 2 (ChildLoader.flagsWord state (.start control)) 0 0 0 0

def loaderTraceNames : List String :=
  [ "loader-trace.rollback-below-range"
  , "loader-trace.refused-after-rollback"
  , "loader-trace.load-text-in-place"
  , "loader-trace.load-data-copy"
  , "loader-trace.start"
  , "loader-trace.load-after-start"
  , "loader-trace.stale-start-after-start"
  ]

def loaderTraceVectors : List Vector :=
  List.zipWith (fun name step => loaderTraceVector name step.1 step.2) loaderTraceNames
    loaderTraceSteps

/-- The scenario's replies: the rollback (`decision=517`), the refusal
(`decision=257`), the two loads (`decision=1`, `decision=2`), the start
(`decision=3`), and two refusals after the start. -/
theorem loader_trace_replies :
    loaderTraceSteps.map (fun step => (ChildLoader.step step.1 step.2).2) =
      [.rolledBack .outsideAuthority, .refused .noChild, .loaded, .loaded, .started,
        .refused .started, .refused .started] := by
  decide

/-- The trace corpus's expected words. -/
theorem loader_trace_vectors_expected :
    loaderTraceVectors.map (·.expected) = [0x205, 0x101, 1, 2, 3, 0x102, 0x102] := by
  decide

/-- **Every trace vector is the model's reply.**  Each vector's expected word
(the generated decision on the words the model state gives) is the encoded
reply of the loader model's step in that state. -/
theorem loader_trace_vectors_model :
    loaderTraceVectors.map (·.expected) =
      loaderTraceSteps.map (fun step => ChildLoader.encodeReply
        (ChildLoader.requestWritable step.1 step.2) (ChildLoader.step step.1 step.2).2) := by
  decide

/-- The rollback returns the loader to the state before the first spawn. -/
theorem loader_trace_rollback_idle : loaderTraceRolledBack = ChildLoader.rollback loaderTraceIdle := by
  rfl

/-- **The started child reads the admitted bytes**: in place, the text
segment's first file byte; by copy, the data segment's eighth file byte, and
zero just past its file size (the bss word). -/
theorem loader_trace_contents :
    ChildLoader.childByte loaderTraceStarted 0x1000000 = some (UInt8.ofNat (0x1000 % 251)) ∧
      ChildLoader.childByte loaderTraceStarted 0x1001007 = some (UInt8.ofNat (0x2007 % 251)) ∧
      ChildLoader.childByte loaderTraceStarted 0x1001008 = some 0 := by
  decide

end LeanOS.Oracle
