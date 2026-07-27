import LeanOS.BootMemoryMapStreaming

/-!
# Allocation-free production handoff authority

This version-four scalar boundary parses the supported Multiboot2 handoff
directly from its continuous eight-byte stream.  A scan is parameterized by
one boot-accessible frame and returns authority only when that frame has full
usable coverage and no non-usable overlap.  The companion manifest decision
validates the complete, ordered nine-identity reservation vocabulary and
applies the same enclosing-page reservation rule before selection.

All exports are `UInt64`-only and use no Lean runtime allocation.
-/
namespace LeanOS.BootMemoryMapStreamAuthority

def abiVersion : UInt64 := 4
def active : UInt64 := 0
def complete : UInt64 := 1
def rejected : UInt64 := 2

def noError : UInt64 := 0
def badState : UInt64 := 1
def badStream : UInt64 := 2
def badInfoHeader : UInt64 := 3
def badTag : UInt64 := 4
def tooManyTags : UInt64 := 5
def duplicateMap : UInt64 := 6
def badMapLayout : UInt64 := 7
def tooManyEntries : UInt64 := 8
def badEntry : UInt64 := 9
def missingMap : UInt64 := 10
def missingEnd : UInt64 := 11

def phaseInfo : UInt64 := 0
def phaseTag : UInt64 := 1
def phaseIgnored : UInt64 := 2
def phaseMapLayout : UInt64 := 3
def phaseEntryBase : UInt64 := 4
def phaseEntryLength : UInt64 := 5
def phaseEntryType : UInt64 := 6
def phaseDone : UInt64 := 7

def entryLimit : UInt64 := UInt64.ofNat LeanOS.BootMemoryMap.maxEntries

def initialChain : UInt64 := 0xcbf29ce484222325
def chainPrime : UInt64 := 0x100000001b3

def low32 (word : UInt64) : UInt64 := word &&& 0xffffffff
def high32 (word : UInt64) : UInt64 := word >>> 32
private def nextChain (chain chunk : UInt64) : UInt64 :=
  (chain ^^^ chunk) * chainPrime

private def initialError (magic address extent target : UInt64) : UInt64 :=
  if magic != 0x36d76289 then badStream
  else if address % 8 != 0 || address < 4096 then badStream
  else if extent < 16 || extent > 65536 || extent % 8 != 0 then badStream
  else if extent > 0xffffffffffffffff - address then badStream
  else if target >= 4096 then badStream
  else noError

/-! State words are version, status, error, identity, extent, next offset,
continuity chain, parser phase, tag content remaining, tag padded remaining,
saw-map, entry count, pending base, pending length, usable coverage,
non-usable overlap, target frame, highest reported end, and tag count. -/
@[export leanos_boot_decode_init]
def initWord (magic address extent target query : UInt64) : UInt64 :=
  let reason := initialError magic address extent target
  if query == 0 then abiVersion
  else if query == 1 then if reason == noError then active else rejected
  else if query == 2 then reason
  else if reason != noError then 0
  else if query == 3 then address
  else if query == 4 then extent
  else if query == 5 then 0
  else if query == 6 then initialChain
  else if query == 7 then phaseInfo
  else if query == 16 then target
  else 0

/-- Once the scalar initializer's admission conditions hold, every query is
the canonical active parser state.  This isolates initialization from the
later per-chunk parser/coverage induction. -/
theorem initWord_of_admitted
    (address extent target query : UInt64)
    (haligned : address % 8 = 0)
    (hlow : 4096 ≤ address)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hnoOverflow : extent ≤ 0xffffffffffffffff - address)
    (htarget : target < 4096) :
    initWord 0x36d76289 address extent target query =
      if query == 0 then abiVersion
      else if query == 1 then active
      else if query == 2 then noError
      else if query == 3 then address
      else if query == 4 then extent
      else if query == 5 then 0
      else if query == 6 then initialChain
      else if query == 7 then phaseInfo
      else if query == 16 then target
      else 0 := by
  have hnlow : ¬address < 4096 := by simpa using hlow
  have hnextentLow : ¬extent < 16 := by simpa using hextentLow
  have hnextentHigh : ¬65536 < extent := by simpa using hextentHigh
  have hnOverflow : ¬0xffffffffffffffff - address < extent :=
    by simpa using hnoOverflow
  have hntarget : ¬4096 ≤ target := by simpa using htarget
  simp [initWord, initialError, haligned, hextentAligned, hnlow,
    hnextentLow, hnextentHigh, hnOverflow, hntarget]

private def overlap (base stop first past : UInt64) : Bool :=
  base < past && first < stop

def transitionError (version status error identity extent offset phase
    content padded sawMap entries base length usable blocked target
    _highest tagCount streamIdentity streamOffset chunk terminal : UInt64) : UInt64 :=
  if version != abiVersion || status != active || error != noError ||
      identity % 8 != 0 || extent < 16 || extent > 65536 || extent % 8 != 0 ||
      offset >= extent || target >= 4096 || phase > phaseEntryType ||
      usable > 1 || blocked > 1 || sawMap > 1 || tagCount > 64 then badState
  else if streamIdentity != identity || streamOffset != offset ||
      terminal > 1 || ((offset + 8 == extent) != (terminal == 1)) then badStream
  else if phase == phaseInfo then
    if offset != 0 || low32 chunk != extent || high32 chunk != 0 then badInfoHeader
    else noError
  else if phase == phaseTag then
    let tagType := low32 chunk
    let size := high32 chunk
    let remaining := extent - offset
    if tagCount >= 64 then tooManyTags
    else if size < 8 || size > remaining || size > 0xfffffffffffffff8 then badTag
    else
      let rounded := (size + 7) &&& 0xfffffffffffffff8
      if rounded > remaining then badTag
      else if tagType == 0 then
        if size != 8 || offset + 8 != extent then missingEnd
        else if sawMap != 1 then missingMap else noError
      else if tagType == 6 then
        if sawMap != 0 then duplicateMap
        else if size < 16 || (size - 16) % 24 != 0 then badMapLayout
        else if (size - 16) / 24 > entryLimit then tooManyEntries
        else noError
      else noError
  else if phase == phaseIgnored then
    if padded < 8 || content > padded then badState
    else noError
  else if phase == phaseMapLayout then
    if low32 chunk != 24 || high32 chunk != 0 ||
        content % 24 != 0 || content / 24 > entryLimit then badMapLayout
    else noError
  else if phase == phaseEntryType then
    if high32 chunk != 0 || length == 0 ||
        length > 0xffffffffffffffff - base then badEntry
    else if entries >= entryLimit then tooManyEntries
    else noError
  else noError

def nextPhase (phase chunk content padded : UInt64) : UInt64 :=
  if phase == phaseInfo then phaseTag
  else if phase == phaseTag then
    let tagType := low32 chunk
    let size := high32 chunk
    if tagType == 0 then phaseDone
    else if tagType == 6 then phaseMapLayout
    else if ((size + 7) &&& 0xfffffffffffffff8) == 8 then phaseTag
    else phaseIgnored
  else if phase == phaseIgnored then
    if padded == 8 then phaseTag else phaseIgnored
  else if phase == phaseMapLayout then
    if content == 0 then phaseTag else phaseEntryBase
  else if phase == phaseEntryBase then phaseEntryLength
  else if phase == phaseEntryLength then phaseEntryType
  else if phase == phaseEntryType then
    if content == 24 then phaseTag else phaseEntryBase
  else phase

def nextContent (phase chunk content : UInt64) : UInt64 :=
  if phase == phaseTag then
    let tagType := low32 chunk
    let size := high32 chunk
    if tagType == 0 then 0
    else if tagType == 6 then size - 16
    else size - 8
  else if phase == phaseIgnored then
    if content > 8 then content - 8 else 0
  else if phase == phaseEntryType then content - 24
  else content

def nextPadded (phase chunk padded : UInt64) : UInt64 :=
  if phase == phaseTag then
    let tagType := low32 chunk
    let size := high32 chunk
    if tagType == 0 || tagType == 6 then 0
    else ((size + 7) &&& 0xfffffffffffffff8) - 8
  else if phase == phaseIgnored then padded - 8
  else padded

def completedError (reason advanced extent nphase : UInt64) : UInt64 :=
  if reason != noError then reason
  else if advanced == extent && nphase != phaseDone then missingEnd
  else noError

private def entryStop (base length : UInt64) : UInt64 := base + length
private def frameFirst (target : UInt64) : UInt64 := target * 4096
private def framePast (target : UInt64) : UInt64 := target * 4096 + 4096

/-- The scalar entry-type word denotes full target-frame coverage by a usable
Multiboot entry.  This public proof-side predicate names the exact generated
classification test without exposing parser internals. -/
def entryUsableCoverage
    (base length kindWord target : UInt64) : Bool :=
  kindWord &&& 0xffffffff == 1 &&
    base <= target * 4096 &&
    target * 4096 + 4096 <= base + length

/-- The scalar entry-type word denotes any target-frame overlap by a
non-usable Multiboot entry. -/
def entryNonUsableOverlap
    (base length kindWord target : UInt64) : Bool :=
  kindWord &&& 0xffffffff != 1 &&
    base < target * 4096 + 4096 &&
    target * 4096 < base + length

@[export leanos_boot_decode_step]
def stepWord (version status error identity extent offset chain phase content padded
    sawMap entries base length usable blocked target highest tagCount
    streamIdentity streamOffset chunk terminal query : UInt64) : UInt64 :=
  let reason := transitionError version status error identity extent offset phase content padded
    sawMap entries base length usable blocked target highest tagCount streamIdentity streamOffset
    chunk terminal
  let advanced := offset + 8
  let nphase := nextPhase phase chunk content padded
  let ncontent := nextContent phase chunk content
  let npadded := nextPadded phase chunk padded
  let nbase := if phase == phaseEntryBase then chunk else base
  let nlength := if phase == phaseEntryLength then chunk else length
  let stop := entryStop base length
  let entryKind := low32 chunk
  let covered := base <= frameFirst target && framePast target <= stop
  let touches := overlap base stop (frameFirst target) (framePast target)
  let nusable := if phase == phaseEntryType && entryKind == 1 && covered then 1 else usable
  let nblocked := if phase == phaseEntryType && entryKind != 1 && touches then 1 else blocked
  let nentries := if phase == phaseEntryType then entries + 1 else entries
  let nsaw := if phase == phaseTag && low32 chunk == 6 then 1 else sawMap
  let ntagCount := if phase == phaseTag then tagCount + 1 else tagCount
  let nhighest :=
    if phase == phaseEntryType && entryKind == 1 && stop > highest then stop else highest
  let finalReason := completedError reason advanced extent nphase
  if query == 0 then abiVersion
  else if query == 1 then
    if finalReason != noError then rejected
    else if advanced == extent && nphase == phaseDone then complete
    else active
  else if query == 2 then finalReason
  else if finalReason != noError then 0
  else if query == 3 then identity
  else if query == 4 then extent
  else if query == 5 then advanced
  else if query == 6 then nextChain chain chunk
  else if query == 7 then nphase
  else if query == 8 then ncontent
  else if query == 9 then npadded
  else if query == 10 then nsaw
  else if query == 11 then nentries
  else if query == 12 then nbase
  else if query == 13 then nlength
  else if query == 14 then nusable
  else if query == 15 then nblocked
  else if query == 16 then target
  else if query == 17 then nhighest
  else if query == 18 then ntagCount
  else 0

/-- The admitted scalar initializer and the rich information-header word take
one exact canonical step into the tag phase.  This is the first phase-local
induction rule used by the proof-side rich/scalar traversal: every exposed
field is computed by the production transition, not by a parallel parser. -/
theorem infoStepWords_of_admitted
    (address extent target chunk : UInt64)
    (haligned : address % 8 = 0)
    (hlow : 4096 ≤ address)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hnoOverflow : extent ≤ 0xffffffffffffffff - address)
    (htarget : target < 4096)
    (hchunkLow : low32 chunk = extent)
    (hchunkHigh : high32 chunk = 0)
    (hnotFinal : 8 ≠ extent) :
    let initial := fun query =>
      initWord 0x36d76289 address extent target query
    let next := fun query =>
      stepWord
        (initial 0) (initial 1) (initial 2) (initial 3)
        (initial 4) (initial 5) (initial 6) (initial 7)
        (initial 8) (initial 9) (initial 10) (initial 11)
        (initial 12) (initial 13) (initial 14) (initial 15)
        (initial 16) (initial 17) (initial 18)
        address 0 chunk 0 query
    next 0 = abiVersion ∧
      next 1 = active ∧
      next 2 = noError ∧
      next 3 = address ∧
      next 4 = extent ∧
      next 5 = 8 ∧
      next 7 = phaseTag ∧
      next 8 = 0 ∧
      next 9 = 0 ∧
      next 10 = 0 ∧
      next 11 = 0 ∧
      next 12 = 0 ∧
      next 13 = 0 ∧
      next 14 = 0 ∧
      next 15 = 0 ∧
      next 16 = target ∧
      next 17 = 0 ∧
      next 18 = 0 := by
  dsimp only
  have hinit (query : UInt64) :=
    initWord_of_admitted address extent target query haligned hlow
      hextentLow hextentHigh hextentAligned hnoOverflow htarget
  have hextentNotLow : ¬extent < 16 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.le_iff_toNat_le] at hextentLow
    omega
  have hextentNotHigh : ¬65536 < extent := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.le_iff_toNat_le] at hextentHigh
    omega
  have hextentNonzero : extent ≠ 0 := by
    intro h
    rw [h] at hextentLow
    rw [UInt64.le_iff_toNat_le] at hextentLow
    simp at hextentLow
  have htargetNotHigh : ¬4096 ≤ target := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h
    rw [UInt64.lt_iff_toNat_lt] at htarget
    omega
  simp [stepWord, transitionError, completedError, nextPhase,
    nextContent, nextPadded, hinit, hchunkLow, hchunkHigh, haligned,
    hextentNotLow, hextentNotHigh, hextentAligned, hextentNonzero,
    htargetNotHigh, hnotFinal, phaseInfo, phaseTag, phaseDone,
    phaseIgnored, phaseEntryBase, phaseEntryLength, phaseEntryType]

/-- An admitted ignored-tag header advances the scalar cursor to its exact
content/padding counters while preserving every map, entry, and classification
field.  This is the tag-header induction rule used before consuming arbitrary
ignored payload and alignment bytes. -/
theorem ignoredTagHeaderStepWords_of_admitted
    (identity extent offset chain content padded sawMap entries base length
      usable blocked target highest tagCount chunk : UInt64)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (husable : usable ≤ 1)
    (hblocked : blocked ≤ 1)
    (hsawMap : sawMap ≤ 1)
    (htarget : target < 4096)
    (htagCount : tagCount < 64)
    (htypeEnd : low32 chunk ≠ 0)
    (htypeMap : low32 chunk ≠ 6)
    (hsizeLow : 8 ≤ high32 chunk)
    (hsizeFits : high32 chunk ≤ extent - offset)
    (hsizeNoOverflow : high32 chunk ≤ 0xfffffffffffffff8)
    (hroundedFits :
      ((high32 chunk + 7) &&& 0xfffffffffffffff8) ≤ extent - offset) :
    let rounded := (high32 chunk + 7) &&& 0xfffffffffffffff8
    let next := fun query =>
      stepWord
        abiVersion active noError identity extent offset chain phaseTag
        content padded sawMap entries base length usable blocked target highest
        tagCount identity offset chunk 0 query
    next 0 = abiVersion ∧
      next 1 = active ∧
      next 2 = noError ∧
      next 3 = identity ∧
      next 4 = extent ∧
      next 5 = offset + 8 ∧
      next 7 = (if rounded == 8 then phaseTag else phaseIgnored) ∧
      next 8 = high32 chunk - 8 ∧
      next 9 = rounded - 8 ∧
      next 10 = sawMap ∧
      next 11 = entries ∧
      next 12 = base ∧
      next 13 = length ∧
      next 14 = usable ∧
      next 15 = blocked ∧
      next 16 = target ∧
      next 17 = highest ∧
      next 18 = tagCount + 1 := by
  dsimp only
  have hextentNotLow : ¬extent < 16 := by simpa using hextentLow
  have hextentNotHigh : ¬65536 < extent := by simpa using hextentHigh
  have hoffsetNotHigh : ¬extent ≤ offset := by simpa using hoffset
  have htargetNotHigh : ¬4096 ≤ target := by simpa using htarget
  have husableNotHigh : ¬1 < usable := by simpa using husable
  have hblockedNotHigh : ¬1 < blocked := by simpa using hblocked
  have hsawMapNotHigh : ¬1 < sawMap := by simpa using hsawMap
  have htagCountLimit : ¬64 ≤ tagCount := by simpa using htagCount
  have htagCountNotBad : ¬64 < tagCount := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.lt_iff_toNat_lt] at htagCount
    omega
  have hsizeNotLow : ¬high32 chunk < 8 := by simpa using hsizeLow
  have hsizeNotFits : ¬extent - offset < high32 chunk := by
    simpa using hsizeFits
  have hsizeNotOverflow : ¬0xfffffffffffffff8 < high32 chunk := by
    simpa using hsizeNoOverflow
  have hroundedNotFits :
      ¬extent - offset < ((high32 chunk + 7) &&& 0xfffffffffffffff8) := by
    simpa using hroundedFits
  simp [stepWord, transitionError, completedError, nextPhase,
    nextContent, nextPadded, hidentityAligned, hextentNotLow,
    hextentNotHigh, hextentAligned, hoffsetNotHigh, htargetNotHigh,
    husableNotHigh, hblockedNotHigh, hsawMapNotHigh, htagCountLimit,
    htagCountNotBad, htypeEnd, htypeMap, hsizeNotLow, hsizeNotFits,
    hsizeNotOverflow, hroundedNotFits, hoffsetNotFinal,
    phaseInfo, phaseTag, phaseDone, phaseIgnored, phaseEntryBase,
    phaseEntryLength, phaseEntryType]

/-- An admitted ignored-tag body word advances the scalar cursor through
content or alignment padding.  The remaining padded count decreases by one
word, content decreases only while content bytes remain, and every map, entry,
and classification field is preserved. -/
theorem ignoredTagBodyStepWords_of_admitted
    (identity extent offset chain content padded sawMap entries base length
      usable blocked target highest tagCount chunk : UInt64)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (husable : usable ≤ 1)
    (hblocked : blocked ≤ 1)
    (hsawMap : sawMap ≤ 1)
    (htarget : target < 4096)
    (htagCount : tagCount ≤ 64)
    (hpadded : 8 ≤ padded)
    (hcontent : content ≤ padded) :
    let next := fun query =>
      stepWord
        abiVersion active noError identity extent offset chain phaseIgnored
        content padded sawMap entries base length usable blocked target highest
        tagCount identity offset chunk 0 query
    next 0 = abiVersion ∧
      next 1 = active ∧
      next 2 = noError ∧
      next 3 = identity ∧
      next 4 = extent ∧
      next 5 = offset + 8 ∧
      next 7 = (if padded == 8 then phaseTag else phaseIgnored) ∧
      next 8 = (if content > 8 then content - 8 else 0) ∧
      next 9 = padded - 8 ∧
      next 10 = sawMap ∧
      next 11 = entries ∧
      next 12 = base ∧
      next 13 = length ∧
      next 14 = usable ∧
      next 15 = blocked ∧
      next 16 = target ∧
      next 17 = highest ∧
      next 18 = tagCount := by
  dsimp only
  have hextentNotLow : ¬extent < 16 := by simpa using hextentLow
  have hextentNotHigh : ¬65536 < extent := by simpa using hextentHigh
  have hoffsetNotHigh : ¬extent ≤ offset := by simpa using hoffset
  have htargetNotHigh : ¬4096 ≤ target := by simpa using htarget
  have husableNotHigh : ¬1 < usable := by simpa using husable
  have hblockedNotHigh : ¬1 < blocked := by simpa using hblocked
  have hsawMapNotHigh : ¬1 < sawMap := by simpa using hsawMap
  have htagCountNotBad : ¬64 < tagCount := by simpa using htagCount
  have hpaddedNotLow : ¬padded < 8 := by simpa using hpadded
  have hcontentNotHigh : ¬padded < content := by simpa using hcontent
  simp [stepWord, transitionError, completedError, nextPhase,
    nextContent, nextPadded, hidentityAligned, hextentNotLow,
    hextentNotHigh, hextentAligned, hoffsetNotHigh, htargetNotHigh,
    husableNotHigh, hblockedNotHigh, hsawMapNotHigh, htagCountNotBad,
    hpaddedNotLow, hcontentNotHigh, hoffsetNotFinal, phaseInfo, phaseTag,
    phaseDone, phaseIgnored, phaseEntryBase, phaseEntryLength, phaseEntryType]

/-- An admitted unique memory-map header advances the scalar parser into its
layout phase.  It installs the exact entry-byte count, marks the map as seen,
and preserves all pending-entry and classification fields. -/
theorem memoryMapTagHeaderStepWords_of_admitted
    (identity extent offset chain content padded entries base length
      usable blocked target highest tagCount chunk : UInt64)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : offset < extent)
    (hoffsetNotFinal : offset + 8 ≠ extent)
    (husable : usable ≤ 1)
    (hblocked : blocked ≤ 1)
    (htarget : target < 4096)
    (htagCount : tagCount < 64)
    (htype : low32 chunk = 6)
    (hsizeLow : 16 ≤ high32 chunk)
    (hsizeFits : high32 chunk ≤ extent - offset)
    (hsizeNoOverflow : high32 chunk ≤ 0xfffffffffffffff8)
    (hroundedFits :
      ((high32 chunk + 7) &&& 0xfffffffffffffff8) ≤ extent - offset)
    (halignedEntries : (high32 chunk - 16) % 24 = 0)
    (hentryBound : (high32 chunk - 16) / 24 ≤ entryLimit) :
    let next := fun query =>
      stepWord
        abiVersion active noError identity extent offset chain phaseTag
        content padded 0 entries base length usable blocked target highest
        tagCount identity offset chunk 0 query
    next 0 = abiVersion ∧
      next 1 = active ∧
      next 2 = noError ∧
      next 3 = identity ∧
      next 4 = extent ∧
      next 5 = offset + 8 ∧
      next 7 = phaseMapLayout ∧
      next 8 = high32 chunk - 16 ∧
      next 9 = 0 ∧
      next 10 = 1 ∧
      next 11 = entries ∧
      next 12 = base ∧
      next 13 = length ∧
      next 14 = usable ∧
      next 15 = blocked ∧
      next 16 = target ∧
      next 17 = highest ∧
      next 18 = tagCount + 1 := by
  dsimp only
  have hextentNotLow : ¬extent < 16 := by simpa using hextentLow
  have hextentNotHigh : ¬65536 < extent := by simpa using hextentHigh
  have hoffsetNotHigh : ¬extent ≤ offset := by simpa using hoffset
  have htargetNotHigh : ¬4096 ≤ target := by simpa using htarget
  have husableNotHigh : ¬1 < usable := by simpa using husable
  have hblockedNotHigh : ¬1 < blocked := by simpa using hblocked
  have htagCountLimit : ¬64 ≤ tagCount := by simpa using htagCount
  have htagCountNotBad : ¬64 < tagCount := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.lt_iff_toNat_lt] at htagCount
    omega
  have hsizeNotLow : ¬high32 chunk < 8 := by
    intro h
    rw [UInt64.le_iff_toNat_le] at hsizeLow
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [UInt64.toNat_ofNat] at hsizeLow h
    omega
  have hmapSizeNotLow : ¬high32 chunk < 16 := by simpa using hsizeLow
  have hsizeNotFits : ¬extent - offset < high32 chunk := by
    simpa using hsizeFits
  have hsizeNotOverflow : ¬0xfffffffffffffff8 < high32 chunk := by
    simpa using hsizeNoOverflow
  have hroundedNotFits :
      ¬extent - offset < ((high32 chunk + 7) &&& 0xfffffffffffffff8) := by
    simpa using hroundedFits
  have hentryNotHigh : ¬entryLimit < (high32 chunk - 16) / 24 := by
    simpa using hentryBound
  simp [stepWord, transitionError, completedError, nextPhase,
    nextContent, nextPadded, hidentityAligned, hextentNotLow,
    hextentNotHigh, hextentAligned, hoffsetNotHigh, htargetNotHigh,
    husableNotHigh, hblockedNotHigh, htagCountLimit, htagCountNotBad,
    htype, hsizeNotLow, hmapSizeNotLow, hsizeNotFits, hsizeNotOverflow,
    hroundedNotFits, halignedEntries, hentryNotHigh, hoffsetNotFinal,
    phaseInfo, phaseTag, phaseDone, phaseMapLayout,
    phaseEntryBase, phaseEntryLength, phaseEntryType]

/-- An admitted tag cursor consuming the unique terminal end-tag word reaches
the exact successful scalar terminal state.  This is the terminal constructor
of the rich/scalar phase induction; it is stated over the production
transition and does not assume a caller-supplied terminal comparison. -/
theorem endTagStepWords_of_admitted
    (identity extent offset chain content padded entries base length
      usable blocked target highest tagCount chunk : UInt64)
    (hidentityAligned : identity % 8 = 0)
    (hextentLow : 16 ≤ extent)
    (hextentHigh : extent ≤ 65536)
    (hextentAligned : extent % 8 = 0)
    (hoffset : offset + 8 = extent)
    (husable : usable ≤ 1)
    (hblocked : blocked ≤ 1)
    (htarget : target < 4096)
    (htagCount : tagCount < 64)
    (hchunkLow : low32 chunk = 0)
    (hchunkHigh : high32 chunk = 8) :
    let next := fun query =>
      stepWord
        abiVersion active noError identity extent offset chain phaseTag
        content padded 1 entries base length usable blocked target highest
        tagCount identity offset chunk 1 query
    next 0 = abiVersion ∧
      next 1 = complete ∧
      next 2 = noError ∧
      next 3 = identity ∧
      next 4 = extent ∧
      next 5 = extent ∧
      next 7 = phaseDone ∧
      next 8 = 0 ∧
      next 9 = 0 ∧
      next 10 = 1 ∧
      next 11 = entries ∧
      next 12 = base ∧
      next 13 = length ∧
      next 14 = usable ∧
      next 15 = blocked ∧
      next 16 = target ∧
      next 17 = highest ∧
      next 18 = tagCount + 1 := by
  dsimp only
  have hextentNotLow : ¬extent < 16 := by simpa using hextentLow
  have hextentNotHigh : ¬65536 < extent := by simpa using hextentHigh
  have hoffsetLt : offset < extent := by
    have hnat := congrArg UInt64.toNat hoffset
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat] at hnat
    rw [UInt64.le_iff_toNat_le] at hextentHigh
    rw [UInt64.le_iff_toNat_le] at hextentLow
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    have hoffsetBound := UInt64.toNat_lt offset
    omega
  have htargetNotHigh : ¬4096 ≤ target := by simpa using htarget
  have hoffsetNotHigh : ¬extent ≤ offset := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h
    rw [UInt64.lt_iff_toNat_lt] at hoffsetLt
    omega
  have husableNotHigh : ¬1 < usable := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.le_iff_toNat_le] at husable
    omega
  have hblockedNotHigh : ¬1 < blocked := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.le_iff_toNat_le] at hblocked
    omega
  have htagCountLimit : ¬64 ≤ tagCount := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h
    rw [UInt64.lt_iff_toNat_lt] at htagCount
    omega
  have htagCountNotBad : ¬64 < tagCount := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.lt_iff_toNat_lt] at htagCount
    omega
  have hremaining : extent - offset = 8 := by
    symm
    rw [UInt64.eq_sub_iff_add_eq]
    simpa [UInt64.add_comm] using hoffset
  have hrounded : ¬(8 : UInt64) < (15 &&& 0xfffffffffffffff8) := by
    decide
  simp [stepWord, transitionError, completedError, nextPhase,
    nextContent, nextPadded, hidentityAligned, hextentNotLow,
    hextentNotHigh, hextentAligned, hoffsetNotHigh, htargetNotHigh,
    husableNotHigh, hblockedNotHigh, htagCountLimit, htagCountNotBad,
    hremaining, hrounded, hchunkLow, hchunkHigh, hoffset, phaseInfo,
    phaseTag, phaseDone, phaseEntryBase, phaseEntryLength, phaseEntryType]

theorem step_error_word
    version status error identity extent offset chain phase content padded
    sawMap entries base length usable blocked target highest tagCount
    streamIdentity streamOffset chunk terminal :
    stepWord version status error identity extent offset chain phase content padded
      sawMap entries base length usable blocked target highest tagCount
      streamIdentity streamOffset chunk terminal 2 =
      completedError
        (transitionError version status error identity extent offset phase content padded
          sawMap entries base length usable blocked target highest tagCount
          streamIdentity streamOffset chunk terminal)
        (offset + 8) extent (nextPhase phase chunk content padded) := by
  simp [stepWord]

/-- An accepted entry-type transition updates the two coverage accumulators
with exactly the public usable/non-usable classification predicates.  This is
the local semantic bridge used when folding rich decoded entries into the
terminal scalar words. -/
theorem accepted_entryType_classification_words
    version status error identity extent offset chain phase content padded
    sawMap entries base length usable blocked target highest tagCount
    streamIdentity streamOffset chunk terminal
    (hphase : phase = phaseEntryType)
    (haccepted :
      stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 2 = noError) :
    stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 14 =
      (if entryUsableCoverage base length chunk target then 1 else usable) ∧
    stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 15 =
      (if entryNonUsableOverlap base length chunk target then 1 else blocked) := by
  subst phase
  have hfinal :
      completedError
          (transitionError version status error identity extent offset
            phaseEntryType content padded
            sawMap entries base length usable blocked target highest tagCount
            streamIdentity streamOffset chunk terminal)
          (offset + 8) extent
            (nextPhase phaseEntryType chunk content padded) =
        noError := by
    simpa [stepWord] using haccepted
  simp [stepWord, hfinal, entryUsableCoverage,
    entryNonUsableOverlap, low32, frameFirst, framePast, entryStop, overlap,
    and_assoc]

/-- An accepted transition outside the entry-type phase cannot alter either
entry-classification accumulator.  This is the complementary local case used
by whole-replay induction: headers, tag headers, ignored contents, map layout,
entry bases, and entry lengths all preserve the accumulated classification. -/
theorem accepted_nonEntry_preserves_classification_words
    version status error identity extent offset chain phase content padded
    sawMap entries base length usable blocked target highest tagCount
    streamIdentity streamOffset chunk terminal
    (hphase : phase ≠ phaseEntryType)
    (haccepted :
      stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 2 = noError) :
    stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 14 = usable ∧
    stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 15 = blocked := by
  have hfinal :
      completedError
          (transitionError version status error identity extent offset phase content padded
            sawMap entries base length usable blocked target highest tagCount
            streamIdentity streamOffset chunk terminal)
          (offset + 8) extent (nextPhase phase chunk content padded) =
        noError := by
    simpa [stepWord] using haccepted
  simp [stepWord, hfinal, hphase]

/-- Every rejected scalar transition is fail-closed for arbitrary caller state:
only ABI version, rejected status, and the typed error remain observable. -/
theorem rejected_step_exposes_no_state
    version status error identity extent offset chain phase content padded
    sawMap entries base length usable blocked target highest tagCount
    streamIdentity streamOffset chunk terminal query
    (hrejected :
      stepWord version status error identity extent offset chain phase content padded
        sawMap entries base length usable blocked target highest tagCount
        streamIdentity streamOffset chunk terminal 2 != noError)
    (hzero : query ≠ 0) (hone : query ≠ 1) (htwo : query ≠ 2) :
    stepWord version status error identity extent offset chain phase content padded
      sawMap entries base length usable blocked target highest tagCount
      streamIdentity streamOffset chunk terminal query = 0 := by
  rw [step_error_word] at hrejected
  simp only [stepWord, hzero, hone, htwo, beq_iff_eq, ↓reduceIte]
  rw [if_pos hrejected]

def validRange (start length : UInt64) : Bool :=
  length != 0 && length <= 0xffffffffffffffff - start

def physicalByteLimit : UInt64 :=
  UInt64.ofNat LeanOS.BootMemoryMap.physicalLimit

def withinPhysicalLimit (start length : UInt64) : Bool :=
  validRange start length && start + length <= physicalByteLimit

def contained (outerStart outerLength start length : UInt64) : Bool :=
  validRange outerStart outerLength && validRange start length &&
    outerStart <= start && start + length <= outerStart + outerLength

private def reserved (frame start length : UInt64) : Bool :=
  overlap start (start + length) (frameFirst frame) (framePast frame)

def roundedFirst (start : UInt64) : UInt64 :=
  start / 4096

def roundedPast (start length : UInt64) : UInt64 :=
  let stop := start + length
  stop / 4096 + if stop % 4096 == 0 then 0 else 1

def roundedDisjoint
    (leftStart leftLength rightStart rightLength : UInt64) : Bool :=
  roundedPast leftStart leftLength <= roundedFirst rightStart ||
    roundedPast rightStart rightLength <= roundedFirst leftStart

def manifestValid
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) : Bool :=
  lowStart == 0 && lowLength == 0x100000 &&
    withinPhysicalLimit imageStart imageLength &&
    contained imageStart imageLength pageStart pageLength &&
    contained imageStart imageLength descriptorStart descriptorLength &&
    contained imageStart imageLength stacksStart stacksLength &&
    contained imageStart imageLength guardStart guardLength &&
    contained imageStart imageLength entryStart entryLength &&
    contained imageStart imageLength usersStart usersLength &&
    withinPhysicalLimit infoStart infoLength && infoStart % 8 == 0 &&
    guardLength == 4096 && entryLength != 0 &&
    guardStart + guardLength == entryStart &&
    roundedPast guardStart guardLength == roundedFirst entryStart &&
    roundedDisjoint guardStart guardLength pageStart pageLength &&
    roundedDisjoint entryStart entryLength pageStart pageLength &&
    roundedDisjoint guardStart guardLength descriptorStart descriptorLength &&
    roundedDisjoint entryStart entryLength descriptorStart descriptorLength &&
    roundedDisjoint guardStart guardLength stacksStart stacksLength &&
    roundedDisjoint entryStart entryLength stacksStart stacksLength &&
    roundedDisjoint guardStart guardLength usersStart usersLength &&
    roundedDisjoint entryStart entryLength usersStart usersLength

/-! The positional arguments are the canonical identities:
low memory, loaded image, page tables, descriptor tables, kernel stacks,
ordinary-entry guard, ordinary-entry stack, embedded users, and Multiboot info.
All image-owned subranges must lie within the loaded image.  The ordinary guard
and stack must be exact adjacent rounded frame intervals, disjoint after
rounding from page tables, descriptor tables, other kernel stacks, and embedded
users.  The loaded image and independent Multiboot reservation must end at or
below the canonical `BootMemoryMap.physicalLimit`; containment then applies the
same bound to every image-owned subrange. -/
@[export leanos_boot_manifest_candidate]
def manifestCandidate (frame
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) : UInt64 :=
  let valid := frame < 4096 && manifestValid
    lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength guardStart guardLength
    entryStart entryLength usersStart usersLength infoStart infoLength
  let excluded :=
    reserved frame lowStart lowLength || reserved frame imageStart imageLength ||
    reserved frame pageStart pageLength || reserved frame descriptorStart descriptorLength ||
    reserved frame stacksStart stacksLength || reserved frame guardStart guardLength ||
    reserved frame entryStart entryLength || reserved frame usersStart usersLength ||
    reserved frame infoStart infoLength
  if valid && !excluded then 1 else 0

@[export leanos_boot_manifest_start]
def manifestStart
    (lowStart lowLength imageStart imageLength pageStart pageLength
    descriptorStart descriptorLength stacksStart stacksLength
    guardStart guardLength entryStart entryLength usersStart usersLength
    infoStart infoLength : UInt64) : UInt64 :=
  if !manifestValid lowStart lowLength imageStart imageLength pageStart pageLength
      descriptorStart descriptorLength stacksStart stacksLength guardStart guardLength
      entryStart entryLength usersStart usersLength infoStart infoLength then 4096
  else
    let lowPast := (lowStart + lowLength + 4095) / 4096
    if lowPast < 4096 then lowPast else 4096

/-- Allocation-free consumer for the exact candidate projection.  The
proof-only scalar/rich equivalence module establishes that the four projection
fields are precisely the rich decoded usable, non-usable-overlap, and
reservation predicates. -/
@[export leanos_boot_consume_exact_projection]
def consumeExactProjection
    (current candidate decodeStatus usable blocked manifest : UInt64) : UInt64 :=
  if current < 4096 then current
  else if candidate < 4096 && decodeStatus == complete && usable == 1 &&
      blocked == 0 && manifest == 1 then candidate
  else 4096

/-- Proof-side compatibility name.  It is intentionally not exported and
final-ELF policy rejects the former `leanos_boot_select_frame` symbol. -/
def selectFrame (current candidate decodeStatus usable blocked manifest : UInt64) : UInt64 :=
  consumeExactProjection current candidate decodeStatus usable blocked manifest

@[export leanos_boot_publish_authority]
def publishAuthority (selected rescanned status usable blocked manifest scrubbed : UInt64) :
    UInt64 :=
  if selected < 4096 && rescanned == selected && status == complete &&
      usable == 1 && blocked == 0 && manifest == 1 && scrubbed == 1 then selected + 1 else 0

theorem selection_deterministic current candidate status usable blocked manifest first second
    (hfirst : selectFrame current candidate status usable blocked manifest = first)
    (hsecond : selectFrame current candidate status usable blocked manifest = second) :
    first = second := by
  rw [hfirst] at hsecond
  exact hsecond

namespace Fixtures

example : manifestCandidate 800 0 0x100000 0x100000 0x200000
    0x110000 0x1000 0x120000 0x1000 0x130000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x180000 0x2000 0x300000 96 = 1 := by decide
example : manifestCandidate 1 0 0x100000 0x100000 0x200000
    0x110000 0x1000 0x120000 0x1000 0x130000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x180000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 800 0 0x100000 0x100000 0x200000
    0x140000 0x1000 0x120000 0x1000 0x130000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x180000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 800 0 0x100000 0x100000 0x200000
    0x110000 0x1000 0x141000 0x1000 0x130000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x180000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 800 0 0x100000 0x100000 0x200000
    0x110000 0x1000 0x120000 0x1000 0x140000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x180000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 800 0 0x100000 0x100000 0x200000
    0x110000 0x1000 0x120000 0x1000 0x130000 0x1000
    0x140000 0x1000 0x141000 0x4000 0x141000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 256 0 0x100000 0xf00000 0x100000
    0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
    0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0x300000 96 = 1 := by decide
example : manifestCandidate 256 0 0x100000 0xf00000 0x100000
    0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
    0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0xffffa0 96 = 1 := by decide
example : manifestCandidate 256 0 0x100000 0xf00000 0x100001
    0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
    0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0x300000 96 = 0 := by decide
example : manifestCandidate 256 0 0x100000 0x200000 0x100000
    0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
    0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0xfffff0 96 = 0 := by decide
example : manifestStart 0 0x100000 0xf00000 0x100001
    0xf10000 0x1000 0xf20000 0x1000 0xf30000 0x1000
    0xf40000 0x1000 0xf41000 0x4000 0xf80000 0x2000 0x300000 96 = 4096 := by decide
example : manifestStart 0 0x100000 0x200000 0x100000
    0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
    0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0xfffff0 96 = 4096 := by decide
example : manifestStart 0 0x100000 0x200000 0x100000
    0x210000 0x1000 0x220000 0x1000 0x230000 0x1000
    0x240000 0x1000 0x241000 0x4000 0x280000 0x2000 0x300000 96 = 256 := by decide
example : selectFrame 4096 300 complete 1 0 1 = 300 := by decide
example : publishAuthority 300 300 complete 1 0 1 1 = 301 := by decide
example : publishAuthority 300 301 complete 1 0 1 1 = 0 := by decide

end Fixtures

end LeanOS.BootMemoryMapStreamAuthority
