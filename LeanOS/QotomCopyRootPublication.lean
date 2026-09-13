/-!
# Qotom bounded copy-root publication checkpoint

This scalar boundary admits the exact first Qotom root construction and a
sixteen-byte cross-page copy-in only after the machine adapter reports both
root scans, two mandatory reload paths, closed-root readback, and byte
agreement.  It publishes no CPL3 authority because production entry and
return integration remain separate obligations.
-/
namespace LeanOS.QotomCopyRootPublication

def alignedArenaRoot (root : UInt64) : Bool :=
  root != 0 && root < 0x1000000 && root &&& 0xfff == 0

/-- Stable bits cover the builder result, selected-image inventory and alias
counts, root identities, machine scans, transfer length/data, and final active
closed root. Zero is the only accepted error mask. -/
def errorMask (builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot : UInt64) : UInt64 :=
  (if builderStatus == 0 then 0 else 1) +
  (if protectedCount == 5 then 0 else 2) +
  (if removed == 3 && retained == 4088 then 0 else 4) +
  (if aliases == 2 then 0 else 8) +
  (if alignedArenaRoot closedRoot then 0 else 16) +
  (if alignedArenaRoot copyRoot && copyRoot != closedRoot then 0 else 32) +
  (if closedScan == 1 then 0 else 64) +
  (if copyScan == 1 then 0 else 128) +
  (if transferred == 16 then 0 else 256) +
  (if bytesMatch == 1 then 0 else 512) +
  (if activeRoot == closedRoot then 0 else 1024)

def accepted (builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot : UInt64) : Bool :=
  errorMask builderStatus protectedCount removed retained aliases closedRoot
    copyRoot closedScan copyScan transferred bytesMatch activeRoot == 0

/-- Words are ABI, acceptance, error mask, closed-root publication,
copy-root publication, completed bytes, CPL3 authority, and next-checkpoint
identity. Root publication means an audited reload selected the constructed
root and read it back; it does not imply entry-path coverage. -/
def query (builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot word : UInt64) : UInt64 :=
  let ok := accepted builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot
  if word == 0 then 1
  else if word == 1 then if ok then 1 else 2
  else if word == 2 then errorMask builderStatus protectedCount removed retained
    aliases closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot
  else if word == 3 then if ok then 1 else 0
  else if word == 4 then if ok then 1 else 0
  else if word == 5 then if ok then transferred else 0
  else if word == 7 then 1
  else 0

theorem query_never_authorizes_cpl3 builderStatus protectedCount removed retained
    aliases closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot :
    query builderStatus protectedCount removed retained aliases closedRoot copyRoot
      closedScan copyScan transferred bytesMatch activeRoot 6 = 0 := by
  simp [query]

theorem publication_requires_acceptance builderStatus protectedCount removed retained
    aliases closedRoot copyRoot closedScan copyScan transferred bytesMatch
    activeRoot
    (h : query builderStatus protectedCount removed retained aliases closedRoot
      copyRoot closedScan copyScan transferred bytesMatch activeRoot 3 = 1) :
    accepted builderStatus protectedCount removed retained aliases closedRoot
      copyRoot closedScan copyScan transferred bytesMatch activeRoot = true := by
  simpa [query] using h

example : query 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1
    0x300000 1 = 1 := by decide
example : query 0 5 3 4088 2 0x300000 0x30b000 1 1 15 1
    0x300000 1 = 2 := by decide
example : query 0 5 3 4088 2 0x300000 0x30b000 1 1 16 1
    0x300000 6 = 0 := by decide

@[export leanos_qotom_copy_root_publication_query]
def exportedQuery (builderStatus protectedCount removed retained aliases
    closedRoot copyRoot closedScan copyScan transferred bytesMatch activeRoot
    word : UInt64) : UInt64 :=
  query builderStatus protectedCount removed retained aliases closedRoot copyRoot
    closedScan copyScan transferred bytesMatch activeRoot word

end LeanOS.QotomCopyRootPublication
