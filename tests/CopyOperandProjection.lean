import LeanOS.UserCopyOperands

open LeanOS LeanOS.VirtualMapping LeanOS.UserCopy LeanOS.UserCopyAliases LeanOS.UserCopyOperands

-- Test-only bridge for accepted, prevalidated locations. This does not bypass
-- or exercise UserCopy.validate; its authority is a separate caller obligation.
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
    if words.size < 4 then throw (IO.userError "short test row")
    let count := words[0]!
    let out := words[1]! == 1
    let base := words[2]!
    let buffer := words[3]!
    if count > 16 || words.size != 4 + count*2 then
      throw (IO.userError "invalid test shape")
    let locations : List Location := (List.range count).map fun i =>
      { virtualPage := 0, frame := words[4+2*i]!, offset := words[5+2*i]! }
    let frames := (locations.map Location.frame).eraseDups
    if frames.length > 2 then throw (IO.userError "too many frames")
    let access : Access := if out then .write else .read
    let ancestor : X86PageTable.Ancestor := { present := true, writable := true, user := true }
    let closed : X86PageTable.PageTable :=
      { pml4 := ancestor, pdpt := ancestor, pd := ancestor, leaf := fun _ => none }
    let table := project closed base frames access
    let plan : Plan := { locations, frames, table }
    let leaves := (List.range 2).map fun i =>
      match table.leaf (base+i) with
      | none => 0
      | some leaf => leaf.frame*4096 + 1 + (if leaf.writable then 2 else 0) +
          (if leaf.noExecute then 2^63 else 0) + (if leaf.user then 4 else 0)
    let pairs := ((operands plan base).zipIdx).flatMap fun (op, i) =>
      let alias := op.page*4096 + op.offset
      if out then [buffer+i, alias] else [alias, buffer+i]
    output.putStrLn (String.intercalate " " ((leaves ++ pairs).map toString))
