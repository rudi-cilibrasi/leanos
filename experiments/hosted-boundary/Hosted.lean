def transition (state command : UInt64) : UInt64 :=
  state ^^^ command

def main : IO Unit := do
  let result := transition 0x55 0x0f
  if result != 0x5a then
    throw <| IO.userError s!"unexpected result: {result}"
  IO.println s!"LEANOS-HOSTED result={result}"
