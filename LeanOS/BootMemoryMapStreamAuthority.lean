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

private def low32 (word : UInt64) : UInt64 := word &&& 0xffffffff
private def high32 (word : UInt64) : UInt64 := word >>> 32
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

private def overlap (base stop first past : UInt64) : Bool :=
  base < past && first < stop

private def transitionError (version status error identity extent offset phase
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

private def nextPhase (phase chunk content padded : UInt64) : UInt64 :=
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

private def nextContent (phase chunk content : UInt64) : UInt64 :=
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

private def nextPadded (phase chunk padded : UInt64) : UInt64 :=
  if phase == phaseTag then
    let tagType := low32 chunk
    let size := high32 chunk
    if tagType == 0 || tagType == 6 then 0
    else ((size + 7) &&& 0xfffffffffffffff8) - 8
  else if phase == phaseIgnored then padded - 8
  else padded

private def entryStop (base length : UInt64) : UInt64 := base + length
private def frameFirst (target : UInt64) : UInt64 := target * 4096
private def framePast (target : UInt64) : UInt64 := target * 4096 + 4096

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
  if query == 0 then abiVersion
  else if query == 1 then
    if reason != noError then rejected
    else if advanced == extent && nphase == phaseDone then complete
    else if advanced == extent then rejected else active
  else if query == 2 then
    if reason != noError then reason
    else if advanced == extent && nphase != phaseDone then missingEnd else noError
  else if reason != noError then 0
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

private def validRange (start length : UInt64) : Bool :=
  length != 0 && length <= 0xffffffffffffffff - start

private def physicalByteLimit : UInt64 :=
  UInt64.ofNat LeanOS.BootMemoryMap.physicalLimit

private def withinPhysicalLimit (start length : UInt64) : Bool :=
  validRange start length && start + length <= physicalByteLimit

private def contained (outerStart outerLength start length : UInt64) : Bool :=
  validRange outerStart outerLength && validRange start length &&
    outerStart <= start && start + length <= outerStart + outerLength

private def reserved (frame start length : UInt64) : Bool :=
  overlap start (start + length) (frameFirst frame) (framePast frame)

private def roundedFirst (start : UInt64) : UInt64 :=
  start / 4096

private def roundedPast (start length : UInt64) : UInt64 :=
  let stop := start + length
  stop / 4096 + if stop % 4096 == 0 then 0 else 1

private def roundedDisjoint
    (leftStart leftLength rightStart rightLength : UInt64) : Bool :=
  roundedPast leftStart leftLength <= roundedFirst rightStart ||
    roundedPast rightStart rightLength <= roundedFirst leftStart

private def manifestValid
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

@[export leanos_boot_select_frame]
def selectFrame (current candidate decodeStatus usable blocked manifest : UInt64) : UInt64 :=
  if current < 4096 then current
  else if candidate < 4096 && decodeStatus == complete && usable == 1 &&
      blocked == 0 && manifest == 1 then candidate
  else 4096

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
