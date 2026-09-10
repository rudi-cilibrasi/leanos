import LeanOS.UserCopyBinding

open LeanOS LeanOS.VirtualMapping LeanOS.UserCopy LeanOS.X86PageTable

private def code : UserCopyBinding.Error → Nat
  | .hardwareMismatch => 12
  | .validation .tooLong => 1
  | .validation .overflow => 2
  | .validation .nonCanonical => 3
  | .validation .aliased => 11
  | .validation (.translation .invalidAddressSpace) => 4
  | .validation (.translation .notOwner) => 5
  | .validation (.translation .unmappedPage) => 6
  | .validation (.translation .missingPermission) => 7
  | .validation (.translation .kindMismatch) => 8
  | .validation (.translation .retiredObject) => 9
  | .validation (.translation .allocatorMismatch) => 10

private def ancestor (word : Nat) : Ancestor :=
  { present := word % 2 == 1, writable := word / 2 % 2 == 1, user := word / 4 % 2 == 1 }
private def leaf (word : Nat) : Leaf :=
  { frame := word / 4096 % 2^40, present := word % 2 == 1
    writable := word / 2 % 2 == 1, user := word / 4 % 2 == 1
    noExecute := word / 2^63 % 2 == 1
    reservedBitsClear := (word &&& 0x800ffffffffff067) == word }

-- Test-only bridge. Corpus records are globally consistent and have uniform
-- ancestor words, matching this model's shared-ancestor table representation.
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let mut w : Array Nat := #[]
    for field in line.trimAscii.toString.splitOn " " do
      let some n := field.toNat? | throw (IO.userError "invalid test word")
      w := w.push n
    if w.size != 35 || w[8]! > 2 then throw (IO.userError "invalid row shape")
    let rows := (List.range w[8]!).map fun i => w.extract (9+13*i) (22+13*i)
    let objectRow := fun object => rows.find? fun r => r[1]! == object
    let frameRow := fun frame => rows.find? fun r => r[5]! != 0 && r[6]! == frame
    let virtual : VirtualMapping.State :=
      { memory :=
          { capabilities :=
              { subjects := fun _ => true, objects := fun _ => true
                kinds := fun object => (objectRow object).bind fun r =>
                  if r[4]! != 0 then some .memory else none
                slots := fun _ _ => none }
            allocator :=
              { frames := rows.map fun r => r[6]!
                status := fun frame => match frameRow frame with
                  | some r => if r[7]! != 0 then .owned r[8]! else .reserved
                  | none => .reserved }
            binding := fun object => (objectRow object).bind fun r =>
              if r[5]! != 0 then some r[6]! else none
            issued := fun _ => true }
        owner := fun space => if space == w[5]! && w[6]! != 0 then some w[7]! else none
        mappings := fun space page => if space != w[5]! then none else
          (rows.find? fun r => r[0]! == page).map fun r =>
            { object := r[1]!, permissions := { read := r[2]! != 0, write := r[3]! != 0 } }
        issuedAddressSpace := fun _ => true }
    let state : UserCopy.State :=
      { virtual, userBytes := fun _ _ => 0, kernelBytes := fun _ _ => 0 }
    let table : PageTable :=
      { pml4 := ancestor w[18]!, pdpt := ancestor w[19]!, pd := ancestor w[20]!
        leaf := fun page => (rows.find? fun r => r[0]! == page).map fun r => leaf r[12]! }
    let result := UserCopyBinding.bind state
      { caller := w[0]!, activeAddressSpace := w[1]! } (UInt64.ofNat w[2]!) w[3]!
      (if w[4]! == 1 then .write else .read) table
    match result with
    | .error reason => output.putStrLn (toString (code reason))
    | .ok locations =>
      output.putStrLn (String.intercalate " " ((0 :: locations.length ::
        locations.flatMap (fun l => [l.frame, l.offset])).map toString))
