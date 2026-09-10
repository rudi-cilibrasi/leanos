import LeanOS.UserCopyAliases
open LeanOS LeanOS.VirtualMapping LeanOS.UserCopy LeanOS.UserCopyAliases LeanOS.X86PageTable

private def demoVirtual : VirtualMapping.State :=
  { memory :=
      { capabilities :=
          { subjects := fun subject => subject = 0
            objects := fun object => object = 10 || object = 11
            kinds := fun object => if object = 10 || object = 11 then some .memory else none
            slots := fun _ _ => none }
        allocator :=
          { frames := [4, 5]
            status := fun frame => if frame = 4 then .owned 10
              else if frame = 5 then .owned 11 else .reserved }
        binding := fun object => if object = 10 then some 4 else if object = 11 then some 5 else none
        issued := fun object => object = 10 || object = 11 }
    owner := fun space => if space = 7 then some 0 else none
    mappings := fun space page =>
      if space = 7 ∧ page = 0 then some { object := 10, permissions := { read := true, write := true } }
      else if space = 7 ∧ page = 1 then some { object := 11, permissions := { read := true, write := true } }
      else none
    issuedAddressSpace := fun space => space = 7 }

private def demo : UserCopy.State :=
  { virtual := demoVirtual
    userBytes := fun frame offset => UInt8.ofNat (frame * 16 + offset)
    kernelBytes := fun buffer offset => UInt8.ofNat (buffer + offset + 1) }
private def ctx : TrustedContext := { caller := 0, activeAddressSpace := 7 }


private def kernelLeaf : Leaf :=
  { frame := 8, present := true, writable := true, user := false,
    noExecute := false, reservedBitsClear := true }
private def closed : PageTable :=
  { pml4 := { present := true, writable := true, user := true }
    pdpt := { present := true, writable := true, user := true }
    pd := { present := true, writable := true, user := true }
    leaf := fun page => if page = 64 then some kernelLeaf else none }
private def readPlan := prepare demo ctx 4095 2 .read closed 128 [4, 5]
private def writePlan := prepare demo ctx 4095 2 .write closed 128 [4, 5]
private def context (kind : AccessKind) (privilege : Privilege := .supervisor) : AccessContext :=
  { kind, privilege, writeProtect := true, nxEnable := true,
    smep := true, smap := false, ac := false }
private def walkPlan (plan : Except UserCopyAliases.Error Plan) (page : Nat)
    (kind : AccessKind) (privilege : Privilege := .supervisor) :=
  plan.toOption.map (fun p => classify p.table page (context kind privilege))

example : readPlan.toOption.map (·.frames) = some [4, 5] := by rfl
example : walkPlan readPlan 128 .read = some (.ok 4) := by rfl
example : walkPlan readPlan 129 .read = some (.ok 5) := by rfl
example : walkPlan readPlan 128 .write = some (.error .notWritable) := by rfl
example : walkPlan writePlan 128 .write = some (.ok 4) := by rfl
example : walkPlan writePlan 129 .write = some (.ok 5) := by rfl
example : walkPlan writePlan 128 .execute = some (.error .noExecute) := by rfl
example : walkPlan writePlan 128 .read .user = some (.error .supervisor) := by rfl
example : walkPlan readPlan 130 .read = some (.error .notPresent) := by rfl
example : walkPlan readPlan 0 .read = some (.error .notPresent) := by rfl
example : walkPlan readPlan 1 .read = some (.error .notPresent) := by rfl
example : walkPlan readPlan 64 .read = some (.ok 8) := by rfl
-- Multiple validated bytes from one page consume just one alias.
example : (prepare demo ctx 0 16 .read closed 128 [4, 5]).toOption.map (·.frames) = some [4] := by rfl
example : walkPlan (prepare demo ctx 0 16 .read closed 128 [4, 5]) 129 .read = some (.error .notPresent) := by rfl
-- Zero length never maps a user frame, even with an otherwise invalid start.
example : (prepare demo ctx 0xffffffffffffffff 0 .read closed 128 []).toOption.map (·.frames) = some [] := by rfl
example : walkPlan (prepare demo ctx 0 0 .read closed 128 []) 128 .read = some (.error .notPresent) := by rfl
example : prepare demo ctx 4095 2 .read closed 64 [4, 5] = .error .occupiedSlots := by rfl
example : prepare demo ctx 4095 2 .read closed (lowerCanonicalPages - 1) [4, 5] = .error .invalidSlots := by rfl
example : prepare demo ctx 4095 2 .read closed 128 [4] = .error .unprotectedFrame := by rfl
example : prepare demo ctx 8191 2 .read closed 128 [4, 5] = .error (.validation (.translation .unmappedPage)) := by rfl
example : prepare demo ctx 0 17 .read closed 128 [4, 5] = .error (.validation .tooLong) := by rfl
example : prepare demo ctx 0xffffffffffffffff 2 .read closed 128 [4, 5] = .error (.validation .overflow) := by rfl
example : prepare demo { ctx with caller := 1 } 0 1 .read closed 128 [4, 5] = .error (.validation (.translation .notOwner)) := by rfl

-- Abstract mapping authority alone does not make a frame encodable in a PTE.
private def wideFrame : UserCopy.State :=
  { demo with virtual := { demoVirtual with memory :=
      { demoVirtual.memory with
        binding := fun object => if object = 10 then some physicalFrameLimit else none
        allocator := { frames := [physicalFrameLimit]
                       status := fun frame => if frame = physicalFrameLimit then .owned 10 else .reserved } } } }
example : prepare wideFrame ctx 0 1 .read closed 128 [physicalFrameLimit] =
  .error .unrepresentableFrame := by rfl
