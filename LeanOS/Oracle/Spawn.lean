import LeanOS.Oracle.Composite
import LeanOS.SpawnBoundary
import LeanOS.SpawnSyscall
import LeanOS.ChildLoader

/-!
# Oracle corpus: spawn and the run-time loader

The spawn family's edge and hostile rows on the stateful composite dispatcher,
the ring-3 spawn syscall's rows, and the run-time loader's rows, with their
expected-word and model checks.
-/
namespace LeanOS.Oracle

open LeanOS
set_option maxRecDepth 4096

private def spawnSyscallStep (id : String) (state actor number rbx rcx rdx : UInt64) :
    Vector :=
  { id, adapter := "SpawnSyscall.step", words := [state, actor, number, rbx, rcx, rdx],
    expected := SpawnSyscall.spawnSyscall state actor number rbx rcx rdx }

private def spawnSyscallValue (id : String) (state actor number rbx rcx rdx : UInt64) :
    Vector :=
  { id, adapter := "SpawnSyscall.value", words := [state, actor, number, rbx, rcx, rdx],
    expected := SpawnSyscall.spawnSyscallValue state actor number rbx rcx rdx }

private def loaderSource (id : String) (source start stop fileOffset span : UInt64) : Vector :=
  { id, adapter := "ChildLoader.source", words := [source, start, stop, fileOffset, span],
    expected := ChildLoader.loaderSource source start stop fileOffset span }

private def loaderDecide (id : String) (op flags sourceCode pages frames used : UInt64) :
    Vector :=
  { id, adapter := "ChildLoader.decide", words := [op, flags, sourceCode, pages, frames, used],
    expected := ChildLoader.loaderDecide op flags sourceCode pages frames used }

/-- The spawn family (ADR 0010 gate item 5): one vector per edge of
`SpawnBoundary.edges`, in table order. -/
def spawnEdgeNames : List String :=
  [ "composite.spawn-seed-spawn"
  , "composite.spawn-seed-grant-first-control"
  , "composite.spawn-seed-kernel-grant-parent"
  , "composite.spawn-seed-kernel-grant-child"
  , "composite.spawn-authorized-spawn"
  , "composite.spawn-authorized-spawn-generation-two"
  , "composite.spawn-authorized-spawn-malformed-endpoint"
  , "composite.spawn-authorized-spawn-stale-endpoint"
  , "composite.spawn-authorized-spawn-endpoint-out-of-range"
  , "composite.spawn-authorized-spawn-address-space-as-endpoint"
  , "composite.spawn-authorized-spawn-invalid-rights"
  , "composite.spawn-authorized-terminate-first-control"
  , "composite.spawn-authorized-kernel-revoke-parent"
  , "composite.spawn-authorized-allocate-slot-3"
  , "composite.spawn-authorized-copy-send-only"
  , "composite.spawn-authorized-copy-send-grant"
  , "composite.spawn-spawned-spawn"
  , "composite.spawn-spawned-grant-first-control"
  , "composite.spawn-spawned-grant-second-control"
  , "composite.spawn-spawned-grant-malformed-control"
  , "composite.spawn-spawned-release-slot-2"
  , "composite.spawn-spawned-timer-switch"
  , "composite.spawn-spawned-kernel-grant-child"
  , "composite.spawn-released-release-slot-2"
  , "composite.spawn-released-grant-two-frames"
  , "composite.spawn-released-grant-first-control"
  , "composite.spawn-granted-allocate-slot-2"
  , "composite.spawn-granted-terminate-first-control"
  , "composite.spawn-terminated-terminate-first-control"
  , "composite.spawn-terminated-grant-first-control"
  , "composite.spawn-terminated-allocate-slot-2"
  , "composite.spawn-reallocated-spawn"
  , "composite.spawn-respawned-terminate-first-control"
  , "composite.spawn-respawned-grant-first-control"
  , "composite.spawn-respawned-spawn"
  , "composite.spawn-respawned-terminate-second-control"
  , "composite.spawn-other-subject-terminate-first-control"
  , "composite.spawn-other-subject-grant-first-control"
  , "composite.spawn-other-subject-spawn-bystander-endpoint"
  , "composite.spawn-other-subject-allocate-slot-2"
  , "composite.spawn-revoked-spawn"
  , "composite.spawn-revoked-kernel-grant-parent"
  , "composite.spawn-regranted-spawn"
  , "composite.spawn-regranted-spawn-generation-two"
  , "composite.spawn-subjects-exhausted-spawn"
  , "composite.spawn-objects-exhausted-spawn"
  , "composite.spawn-controls-exhausted-spawn"
  , "composite.spawn-narrowed-send-spawn-narrowed-endpoint"
  , "composite.spawn-narrowed-grant-spawn-rights-not-subset"
  , "composite.spawn-terminated-spawn-into-reused-slot"
  , "composite.spawn-loader-respawned-grant-second-control"
  , "composite.spawn-loader-respawned-grant-first-control"
  , "composite.spawn-loader-granted-terminate-second-control"
  , "composite.spawn-loader-granted-terminate-first-control"
  ]

def spawnEdgeVector (name : String) (edge : SpawnBoundary.Edge) : Vector :=
  let words := edge.words
  composite name (SpawnBoundary.encodeState edge.state)
    words.tag words.arg0 words.arg1 words.arg2 words.arg3

def spawnEdgeVectors : List Vector :=
  List.zipWith spawnEdgeVector spawnEdgeNames SpawnBoundary.edges

/-- Hostile encodings against the spawn family's tokens: noncanonical and
reserved arguments, accepted words replayed at the wrong state, splices from
other families, and wrong versions.  Each rejects with an error word before
any gate runs. -/
def spawnNegativeVectors : List Vector := [
  composite "composite.spawn-reserved-rights-bit" 0x7101 0x7001 1 0x30000 64 0,
  composite "composite.spawn-reserved-argument" 0x7101 0x7001 1 0x30000 4 1,
  composite "composite.spawn-zero-spawn-word" 0x7101 0x7001 0 0x30000 4 0,
  composite "composite.spawn-accepted-words-at-wrong-state" 0x7301 0x7001 1 0x30000 4 0,
  composite "composite.spawn-grant-replayed-after-grant" 0x7401 0x7101 0x10000 1 0 0,
  composite "composite.spawn-termination-before-spawn-replay" 0x7001 0x7201 0x10000 0 0 0,
  composite "composite.spawn-caller-forged-in-grant" 0x7201 0x7101 0x10000 1 2 0,
  composite "composite.spawn-release-unnamed-slot" 0x7201 0x7401 9 0 0 0,
  composite "composite.spawn-switch-with-argument" 0x7201 0x7701 1 0 0 0,
  composite "composite.spawn-cross-family-splice" 0x7201 0x0101 1 0 0 0,
  composite "composite.spawn-reserved-command" 0x7201 0x7901 0 0 0 0,
  composite "composite.spawn-wrong-command-version" 0x7201 0x7002 1 0x30000 4 0,
  composite "composite.spawn-wrong-state-version" 0x7102 0x7001 1 0x30000 4 0,
  composite "composite.spawn-state-above-family" 0x8501 0x7001 1 0x30000 4 0]

/-- The ring-3 spawn syscall (#489, #491): the `spawn-child` image's thirteen
calls at their tokens, then every refusal (not a family token, not the current
subject, not a spawn-family number, noncanonical registers for each number,
a decodable command outside the bounded table, maximum words), the bystander
presenting the parent's control word, and the value words of the accepted
calls and of a refusal. -/
def spawnSyscallVectors : List Vector := [
  spawnSyscallStep "spawn-syscall.spawn" 0x7101 2 100 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.reserved-rights-bit" 0x7201 2 100 1 0x30000 0x40,
  spawnSyscallStep "spawn-syscall.subject-budget-exhausted" 0x7201 2 100 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.grant-frame-in-use" 0x7201 2 101 0x10000 1 0,
  spawnSyscallStep "spawn-syscall.release" 0x7201 2 104 2 0 0,
  spawnSyscallStep "spawn-syscall.grant" 0x7301 2 101 0x10000 1 0,
  spawnSyscallStep "spawn-syscall.terminate" 0x7401 2 102 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.terminate-stale" 0x7501 2 102 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.allocate" 0x7501 2 103 2 0 0,
  spawnSyscallStep "spawn-syscall.respawn-same-slot" 0x7601 2 100 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.old-handle-terminate" 0x7701 2 102 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.old-handle-grant" 0x7701 2 101 0x10000 1 0,
  spawnSyscallStep "spawn-syscall.terminate-new-child" 0x7701 2 102 0x20000 0 0,
  spawnSyscallStep "spawn-syscall.not-family-state" 0x0101 2 100 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.not-current-subject" 0x7101 1 100 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.parent-after-switch" 0x7901 2 102 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.bystander-presents-control" 0x7901 1 102 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.kernel-grant-not-a-syscall" 0x7101 2 105 2 1 0,
  spawnSyscallStep "spawn-syscall.number-below-family" 0x7101 2 99 1 0x30000 4,
  spawnSyscallStep "spawn-syscall.zero-spawn-word" 0x7101 2 100 0 0x30000 4,
  spawnSyscallStep "spawn-syscall.grant-zero-frames" 0x7301 2 101 0x10000 0 0,
  spawnSyscallStep "spawn-syscall.grant-reserved-rdx" 0x7301 2 101 0x10000 1 1,
  spawnSyscallStep "spawn-syscall.terminate-reserved-rcx" 0x7401 2 102 0x10000 1 0,
  spawnSyscallStep "spawn-syscall.allocate-reserved-rdx" 0x7501 2 103 2 0 1,
  spawnSyscallStep "spawn-syscall.release-reserved-rcx" 0x7201 2 104 2 1 0,
  spawnSyscallStep "spawn-syscall.outside-table-allocate" 0x7101 2 103 5 0 0,
  spawnSyscallStep "spawn-syscall.outside-table-empty-rights" 0x7101 2 100 1 0x30000 0,
  spawnSyscallStep "spawn-syscall.maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff 0xffffffffffffffff,
  spawnSyscallValue "spawn-syscall-value.spawn" 0x7101 2 100 1 0x30000 4,
  spawnSyscallValue "spawn-syscall-value.grant" 0x7301 2 101 0x10000 1 0,
  spawnSyscallValue "spawn-syscall-value.terminate" 0x7401 2 102 0x10000 0 0,
  spawnSyscallValue "spawn-syscall-value.respawn-same-slot" 0x7601 2 100 1 0x30000 4,
  spawnSyscallValue "spawn-syscall-value.terminate-new-child" 0x7701 2 102 0x20000 0 0,
  spawnSyscallValue "spawn-syscall-value.old-handle-terminate" 0x7701 2 102 0x10000 0 0,
  spawnSyscallValue "spawn-syscall-value.refusal" 0x7201 2 100 1 0x30000 0x40,
  spawnSyscallValue "spawn-syscall-value.outside-table" 0x7101 2 103 5 0 0]

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

/-- The syscall corpus's expected words: the image's thirteen calls answer as
the boot assembly checks (`SpawnSyscall.image_run`), and every refusal vector
answers with its refusal word before any gate. -/
theorem spawn_syscall_vectors_expected :
    spawnSyscallVectors.map (·.expected) =
      [0x017201, 0xfe23, 0x8c7201, 0xc57201, 0x017301, 0x017401, 0x017501, 0xc37501,
        0x017601, 0x017701, 0xc37701, 0xc37701, 0x017801,
        0xfe20, 0xfe21, 0xfe21, 0xc37901, 0xfe22, 0xfe22, 0xfe23, 0xfe23, 0xfe23, 0xfe23,
        0xfe23, 0xfe23, 0xfe24, 0xfe24, 0xfe20,
        0x10000, 1, 1, 0x20000, 0, 0, 0, 0] := by
  decide

/-- Each spawn edge vector carries its edge's words and expects its edge's
reply and value words. -/
theorem spawn_edge_vectors_cover :
    spawnEdgeVectors.length = SpawnBoundary.edges.length ∧
      (List.zip spawnEdgeVectors SpawnBoundary.edges).all (fun pair =>
        let words := pair.2.words
        pair.1.adapter == "CompositeDispatcher.stateful" &&
          pair.1.words == [SpawnBoundary.encodeState pair.2.state, words.tag, words.arg0,
            words.arg1, words.arg2, words.arg3] &&
          pair.1.expected == SpawnBoundary.replyWord pair.2.next pair.2.status &&
          pair.1.expectedValue == pair.2.value) = true := by
  native_decide

/-- **The generated-boundary replay matches the model on every spawn edge
vector.**  The hosted replay compares the generated C of
`leanos_composite_dispatch` and `leanos_composite_dispatch_value` with each
vector's expected words; those are the reply and value words of the family
step (`childGate`, `memoryGate`, or the authoritative gate) on the complete
state the vector's state token names, and that step's post-state is the state
the reply's next-state selector names. -/
theorem spawn_edge_vectors_match_model (plan : BootPageTablePlan.Plan)
    (compiled : BootPageTablePlan.compile BootPageTablePlan.sampleInput = .ok plan)
    (vector : Vector) (edge : SpawnBoundary.Edge)
    (pair : (vector, edge) ∈ List.zip spawnEdgeVectors SpawnBoundary.edges) :
    let outcome := SpawnBoundary.familyStep (SpawnBoundary.stateOf plan edge.state) edge.command
    vector.expected = SpawnBoundary.replyWord edge.next outcome.status ∧
      vector.expectedValue = outcome.value ∧
      outcome.state = SpawnBoundary.stateOf plan edge.next := by
  intro outcome
  have refines := SpawnBoundary.edge_refines plan compiled edge (List.of_mem_zip pair).2
  have covered := List.all_eq_true.1 spawn_edge_vectors_cover.2 _ pair
  simp only [Bool.and_eq_true, beq_iff_eq] at covered
  obtain ⟨⟨⟨_, _⟩, expected⟩, value⟩ := covered
  simp only [outcome, refines]
  exact ⟨expected, value, trivial⟩

/-- Every hostile spawn-family encoding is rejected with an error word and no
value word, before any gate runs. -/
theorem spawn_negative_vectors_reject :
    spawnNegativeVectors.all (fun vector =>
      decide (0xff00 ≤ vector.expected) && vector.expectedValue == 0) = true := by
  native_decide

end LeanOS.Oracle
