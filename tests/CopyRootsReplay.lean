import LeanOS.UserCopyOperands
import LeanOS.UserCopyTransaction
import LeanOS.KernelRootPublication

open LeanOS LeanOS.VirtualMapping LeanOS.UserCopy LeanOS.UserCopyAliases LeanOS.X86PageTable
open LeanOS.UserCopyOperands LeanOS.UserCopyPrefix

/-! Test-only native replay of the composed models. This executable is not a
production ABI or evidence that a processor switched roots. -/
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


private def stale : KernelRootPublication.State :=
  { table := closed, cache := [{ page := 128, context := context .read, frame := 4 }] }

deriving instance DecidableEq for Except

private def checks : List (String × Bool) := [
  ("read-first-frame", decide (walkPlan readPlan 128 .read = some (.ok 4))),
  ("read-second-frame", decide (walkPlan readPlan 129 .read = some (.ok 5))),
  ("read-denies-write", decide (walkPlan readPlan 128 .write = some (.error .notWritable))),
  ("write-second-frame", decide (walkPlan writePlan 129 .write = some (.ok 5))),
  ("alias-denies-execute", decide (walkPlan writePlan 128 .execute = some (.error .noExecute))),
  ("alias-denies-user", decide (walkPlan writePlan 128 .read .user = some (.error .supervisor))),
  ("kernel-map-preserved", decide (walkPlan readPlan 64 .read = some (.ok 8))),
  ("cross-page-operands", decide (readPlan.toOption.map (fun p => operands p 128) =
    some [{ page := 128, offset := 4095 }, { page := 129, offset := 0 }])),
  ("write-prefix", decide ((copyToPrefix demo ctx 4095 2 8 1).userBytes 4 4095 = 9)),
  ("write-suffix-preserved", decide ((copyToPrefix demo ctx 4095 2 8 1).userBytes 5 0 = demo.userBytes 5 0)),
  ("read-prefix", decide ((copyFromPrefix demo ctx 4095 2 8 1).kernelBytes 8 0 = demo.userBytes 4 4095)),
  ("read-suffix-preserved", decide ((copyFromPrefix demo ctx 4095 2 8 1).kernelBytes 8 1 = demo.kernelBytes 8 1)),
  ("rejected-before-write", decide ((copyToPrefix demo ctx 8191 2 8 1).userBytes 5 4095 = demo.userBytes 5 4095)),
  ("zero-length", decide ((prepare demo ctx 0xffffffffffffffff 0 .read closed 128 []).toOption.map (fun p => operands p 128) = some [])),
  ("overflow-rejects", (prepare demo ctx 0xffffffffffffffff 2 .read closed 128 [4, 5]).toOption.isNone),
  ("occupied-slot-rejects", (prepare demo ctx 0 1 .read closed 64 [4, 5]).toOption.isNone),
  ("missing-inventory-rejects", (prepare demo ctx 4095 2 .read closed 128 [4]).toOption.isNone),
  ("stale-hit-without-reload", decide (KernelRootPublication.access
    (KernelRootPublication.replaceOnly stale closed) 128 (context .read) = .ok 4)),
  ("reload-removes-hit", decide (KernelRootPublication.access
    (KernelRootPublication.publish stale closed ⟨false, false⟩).state 128 (context .read) = .error .notPresent)),
  ("pcid-rejects", !(KernelRootPublication.publish stale closed ⟨true, false⟩).accepted),
  ("pge-rejects", !(KernelRootPublication.publish stale closed ⟨false, true⟩).accepted),
  ("all-transaction-outcomes", [UserCopyTransaction.Direction.fromUser, .toUser].all fun direction =>
    [UserCopyTransaction.Stop.finished, .interrupted, .faulted].all fun stop =>
    [UserCopyTransaction.Cleanup.verifiedClosed, .unverified].all fun cleanup =>
    [0, 1, 2, 3].all fun count =>
      decide ((UserCopyTransaction.run demo ctx 4095 2 8 direction count stop cleanup).disposition =
        if stop = .finished ∧ cleanup = .verifiedClosed ∧ count = 2
        then UserCopyTransaction.Disposition.returned else .terminal))]

-- The same corpus is checked by kernel reduction and by the generated native executable.
example : checks.all (·.2) = true := by rfl

def main : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError s!"copy-root replay failed: {name}")
    IO.println s!"copy-root {name} PASS"
  IO.println s!"copy-root replay: {checks.length} checks PASS (including 48 transaction outcomes)"
