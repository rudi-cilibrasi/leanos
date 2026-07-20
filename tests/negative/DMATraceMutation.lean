import LeanOS.DMAQuarantine

open LeanOS DMAQuarantine

private def mutatedMemory : MemoryProjection :=
  { zeroMemoryProjection with physicalMemory := fun _ => 1 }

private def mutatedRuntime : RuntimeState :=
  { q35Runtime with memory := mutatedMemory }

-- A nonfatal DMA trace cannot publish a changed complete runtime projection.
example (trace : QuarantineTrace q35Runtime mutatedRuntime) :
    mutatedRuntime ≠ q35Runtime := by
  exact quarantine_trace_state_unchanged trace
