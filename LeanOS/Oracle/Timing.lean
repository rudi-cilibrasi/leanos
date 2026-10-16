import LeanOS.Oracle.Vector
import LeanOS.TimingChannels

/-!
# Oracle corpus: the cross-subject refusal witness

The rows of `TimingChannels.crossSubjectRefusal` (issue #576, ADR 0028): the
timing-channels image's three requests (naming the live peer, a subject never
issued, and the caller itself), then every word combination the refusal
must pass (no scheduled subject, no target, a latch busy in an entry or
halted, an unknown mode word) and maximum words.
-/
namespace LeanOS.Oracle

open LeanOS

private def crossSubjectRefusal (id : String) (mode scheduled target : UInt64) : Vector :=
  { id, adapter := "TimingChannels.refusal", words := [mode, scheduled, target],
    expected := TimingChannels.crossSubjectRefusal mode scheduled target }

/-- The cross-subject refusal witness's corpus (#576). -/
def timingRefusalVectors : List Vector := [
  crossSubjectRefusal "timing.refuse-peer" 1 2 3,
  crossSubjectRefusal "timing.refuse-unissued" 1 2 10,
  crossSubjectRefusal "timing.pass-own" 1 2 2,
  crossSubjectRefusal "timing.pass-no-target" 1 2 0,
  crossSubjectRefusal "timing.pass-none-scheduled" 1 0 3,
  crossSubjectRefusal "timing.pass-handling" 2 2 3,
  crossSubjectRefusal "timing.pass-halted" 3 2 3,
  crossSubjectRefusal "timing.pass-mode-zero" 0 2 3,
  crossSubjectRefusal "timing.refuse-maximum-target" 1 2 0xffffffffffffffff,
  crossSubjectRefusal "timing.pass-maximum-words" 0xffffffffffffffff 0xffffffffffffffff
    0xffffffffffffffff]

/-- The image's two refusals answer the refusal word and its own request the
pass word; every row with a busy, halted or unknown latch, no scheduled
subject or no target passes. -/
theorem timing_refusal_vectors_expected :
    timingRefusalVectors.map Vector.expected =
      [0xc5, 0xc5, 0, 0, 0, 0, 0, 0, 0xc5, 0] := by
  decide

end LeanOS.Oracle
