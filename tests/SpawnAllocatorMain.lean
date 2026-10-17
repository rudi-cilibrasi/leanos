import LeanOS.SpawnAllocatorVectors

/-- Emit the hosted spawn-allocator corpus (#575). -/
def main : IO Unit := LeanOS.SpawnAllocatorVectors.emit
