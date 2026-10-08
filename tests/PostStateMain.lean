import LeanOS.PostStateProjection

/-- Emit the hosted post-state corpus (#476). -/
def main : IO Unit := LeanOS.PostStateProjection.emit
