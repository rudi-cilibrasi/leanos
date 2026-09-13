/-!
# Qotom blocking-IPC whole-profile admission

This scalar boundary combines the already-gated Qotom PCI, no-SMAP, root,
and entry checkpoints with the exact synchronous blocking-IPC configuration.
It authorizes the selected two-subject CPL3 profile; final success still
requires the separately checked physical transcript.
-/
namespace LeanOS.QotomBlockingIPCIntegration

def alignedArenaRoot (root : UInt64) : Bool :=
  root != 0 && root < 0x1000000 && root &&& 0xfff == 0

def errorMask (pciTrust noSmap entryCheckpoint : UInt64)
    (closedRoot copyInRoot copyOutRoot : UInt64)
    (closedScan copyInScan copyOutScan syscallGate pageFaultGate
      timerGateAbsent picMasked contextBanks modelBindings : UInt64) : UInt64 :=
  (if pciTrust == 1 then 0 else 1) +
  (if noSmap == 1 then 0 else 2) +
  (if entryCheckpoint == 1 then 0 else 4) +
  (if alignedArenaRoot closedRoot then 0 else 8) +
  (if alignedArenaRoot copyInRoot && copyInRoot != closedRoot then 0 else 16) +
  (if alignedArenaRoot copyOutRoot && copyOutRoot != closedRoot &&
      copyOutRoot != copyInRoot then 0 else 32) +
  (if closedScan == 1 && copyInScan == 1 && copyOutScan == 1 then 0 else 64) +
  (if syscallGate == 1 && pageFaultGate == 1 then 0 else 128) +
  (if timerGateAbsent == 1 && picMasked == 1 then 0 else 256) +
  (if contextBanks == 2 then 0 else 512) +
  (if modelBindings == 1 then 0 else 1024)

def accepted (pciTrust noSmap entryCheckpoint : UInt64)
    (closedRoot copyInRoot copyOutRoot : UInt64)
    (closedScan copyInScan copyOutScan syscallGate pageFaultGate
      timerGateAbsent picMasked contextBanks modelBindings : UInt64) : Bool :=
  errorMask pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
    closedScan copyInScan copyOutScan syscallGate pageFaultGate
    timerGateAbsent picMasked contextBanks modelBindings == 0

/-- Words are ABI, admission, error mask, CPL3 authority, expected syscall
entries, recoverable faults, context switches, copy transfers, IPC model
transitions, capability model transitions, and terminal policy identity. -/
def query (pciTrust noSmap entryCheckpoint : UInt64)
    (closedRoot copyInRoot copyOutRoot : UInt64)
    (closedScan copyInScan copyOutScan syscallGate pageFaultGate
      timerGateAbsent picMasked contextBanks modelBindings word : UInt64) : UInt64 :=
  let ok := accepted pciTrust noSmap entryCheckpoint closedRoot copyInRoot
    copyOutRoot closedScan copyInScan copyOutScan syscallGate pageFaultGate
    timerGateAbsent picMasked contextBanks modelBindings
  if word == 0 then 1
  else if word == 1 then if ok then 1 else 2
  else if word == 2 then errorMask pciTrust noSmap entryCheckpoint closedRoot
    copyInRoot copyOutRoot closedScan copyInScan copyOutScan syscallGate
    pageFaultGate timerGateAbsent picMasked contextBanks modelBindings
  else if word == 3 then if ok then 1 else 0
  else if word == 4 then if ok then 8 else 0
  else if word == 5 then if ok then 1 else 0
  else if word == 6 then if ok then 2 else 0
  else if word == 7 then if ok then 2 else 0
  else if word == 8 then if ok then 4 else 0
  else if word == 9 then if ok then 4 else 0
  else if word == 10 then if ok then 1 else 0
  else 0

theorem cpl3_authority_requires_admission pciTrust noSmap entryCheckpoint
    closedRoot copyInRoot copyOutRoot closedScan copyInScan copyOutScan
    syscallGate pageFaultGate timerGateAbsent picMasked contextBanks modelBindings
    (h : query pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
      closedScan copyInScan copyOutScan syscallGate pageFaultGate timerGateAbsent
      picMasked contextBanks modelBindings 3 = 1) :
    accepted pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
      closedScan copyInScan copyOutScan syscallGate pageFaultGate timerGateAbsent
      picMasked contextBanks modelBindings = true := by
  simpa [query] using h

example : query 1 1 1 0x1a0000 0x1b0000 0x1c0000
    1 1 1 1 1 1 1 2 1 1 = 1 := by decide
example : query 1 1 1 0x1a0000 0x1b0000 0x1c0000
    1 1 1 1 1 0 1 2 1 1 = 2 := by decide
example : query 1 1 1 0x1a0000 0x1b0000 0x1b0000
    1 1 1 1 1 1 1 2 1 3 = 0 := by decide

@[export leanos_qotom_blocking_ipc_integration_query]
def exportedQuery (pciTrust noSmap entryCheckpoint : UInt64)
    (closedRoot copyInRoot copyOutRoot : UInt64)
    (closedScan copyInScan copyOutScan syscallGate pageFaultGate
      timerGateAbsent picMasked contextBanks modelBindings word : UInt64) : UInt64 :=
  query pciTrust noSmap entryCheckpoint closedRoot copyInRoot copyOutRoot
    closedScan copyInScan copyOutScan syscallGate pageFaultGate timerGateAbsent
    picMasked contextBanks modelBindings word

end LeanOS.QotomBlockingIPCIntegration
