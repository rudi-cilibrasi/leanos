/-!
# Qotom no-SMAP CPL3 entry checkpoint

This scalar boundary accepts the first machine entry/return exercise only when
two CPL3 entries, one completed return, a full saved register bank, closed-root
readback, and the return reload are all reported with exact root identities.
The checkpoint publishes no general CPL3 or IPC authority.
-/
namespace LeanOS.QotomEntryIntegration

def alignedArenaRoot (root : UInt64) : Bool :=
  root != 0 && root < 0x1000000 && root &&& 0xfff == 0

def errorMask (entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload : UInt64) : UInt64 :=
  (if entries == 2 then 0 else 1) +
  (if returns == 1 then 0 else 2) +
  (if alignedArenaRoot incomingRoot then 0 else 4) +
  (if alignedArenaRoot closedRoot && closedRoot != incomingRoot then 0 else 8) +
  (if activeRoot == closedRoot then 0 else 16) +
  (if frame == 1 then 0 else 32) +
  (if userIf == 0 then 0 else 64) +
  (if gprs == 15 then 0 else 128) +
  (if closeReadback == 1 then 0 else 256) +
  (if returnReload == 1 then 0 else 512)

def accepted (entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload : UInt64) : Bool :=
  errorMask entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload == 0

/-- Words are ABI, acceptance, error mask, frame/GPR validation, closed-root
entry, completed return, CPL3 authority, and next-checkpoint identity. -/
def query (entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload word : UInt64) : UInt64 :=
  let ok := accepted entries returns incomingRoot closedRoot activeRoot frame userIf
    gprs closeReadback returnReload
  if word == 0 then 1
  else if word == 1 then if ok then 1 else 2
  else if word == 2 then errorMask entries returns incomingRoot closedRoot
    activeRoot frame userIf gprs closeReadback returnReload
  else if word == 3 then if ok then 1 else 0
  else if word == 4 then if ok then 1 else 0
  else if word == 5 then if ok then returns else 0
  else if word == 7 then 1
  else 0

theorem query_never_authorizes_cpl3 entries returns incomingRoot closedRoot
    activeRoot frame userIf gprs closeReadback returnReload :
    query entries returns incomingRoot closedRoot activeRoot frame userIf gprs
      closeReadback returnReload 6 = 0 := by
  simp [query]

theorem checkpoint_claim_requires_acceptance entries returns incomingRoot
    closedRoot activeRoot frame userIf gprs closeReadback returnReload
    (h : query entries returns incomingRoot closedRoot activeRoot frame userIf gprs
      closeReadback returnReload 3 = 1) :
    accepted entries returns incomingRoot closedRoot activeRoot frame userIf gprs
      closeReadback returnReload = true := by
  simpa [query] using h

example : query 2 1 0x1a0000 0x1a2000 0x1a2000 1 0 15 1 1 1 = 1 := by decide
example : query 2 0 0x1a0000 0x1a2000 0x1a2000 1 0 15 1 1 1 = 2 := by decide
example : query 2 1 0x1a0000 0x1a2000 0x1a2000 1 0 15 1 1 6 = 0 := by decide

@[export leanos_qotom_entry_integration_query]
def exportedQuery (entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload word : UInt64) : UInt64 :=
  query entries returns incomingRoot closedRoot activeRoot frame userIf gprs
    closeReadback returnReload word

end LeanOS.QotomEntryIntegration
