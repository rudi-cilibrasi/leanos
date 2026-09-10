import LeanOS.KernelUserRoot

open LeanOS LeanOS.X86PageTable

-- Test-only canonical leaf-word adapter. A/D and other unmodeled bits are
-- excluded from the differential corpus; their exact preservation is tested in C.
private def decode (word : Nat) : Leaf :=
  { frame := word / 4096 % 2^40
    present := word % 2 = 1
    writable := word / 2 % 2 = 1
    user := word / 4 % 2 = 1
    noExecute := word / 2^63 % 2 = 1
    reservedBitsClear := true }

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let mut words : Array Nat := #[]
    for field in line.trimAscii.toString.splitOn " " do
      let some n := field.toNat? | throw (IO.userError "invalid test word")
      words := words.push n
    if words.size < 2 then throw (IO.userError "short test row")
    let fc := words[0]!
    let rc := words[1]!
    if fc > 16 || rc > 4096 || words.size != 2 + fc + 2*rc + 4096 then
      throw (IO.userError "invalid test shape")
    let frames := (words.extract 2 (2+fc)).toList
    let required := (List.range rc).map fun i =>
      (words[2+fc+2*i]!, decode words[3+fc+2*i]!)
    let source := words.extract (2+fc+2*rc) words.size
    let ancestor : Ancestor := { present := true, writable := true, user := true }
    let table : PageTable :=
      { pml4 := ancestor, pdpt := ancestor, pd := ancestor
        leaf := fun page => match source[page]? with
          | none => none
          | some 0 => none
          | some word => some (decode word) }
    match KernelUserRoot.closeChecked table frames required with
    | none => output.putStrLn "0"
    | some result =>
      let leaves := (List.range 4096).map fun page =>
        toString (if (result.leaf page).isSome then source[page]! else 0)
      output.putStrLn ("1 " ++ String.intercalate " " leaves)
