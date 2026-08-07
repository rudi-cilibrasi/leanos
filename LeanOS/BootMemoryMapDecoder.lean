import LeanOS.BootMemoryMap
import LeanOS.BootTopology

/-!
# Bounded Multiboot2 byte decoder

This module owns the model-side boundary between an immutable byte copy of a
Multiboot2 information structure and `BootMemoryMap.Handoff`.  Copying bytes
from physical memory remains outside the model.  Once copied, every load is
checked against the finite list and every accepted result carries evidence that
the existing typed handoff validator accepts exactly the decoded entries.
-/
namespace LeanOS.BootMemoryMapDecoder

open LeanOS.BootMemoryMap

structure Input where
  magic : Nat
  infoAddress : Nat
  bytes : List UInt8
  deriving BEq, DecidableEq, Repr

inductive Error where
  | badMagic
  | unalignedInfo
  | infoAddressBelowMinimum
  | bufferTooSmall
  | bufferTooLarge
  | truncatedField
  | advertisedSizeMismatch
  | nonzeroInfoReserved
  | tooManyTags
  | malformedTagSize
  | tagOutOfBounds
  | missingEndTag
  | misplacedEndTag
  | missingMemoryMap
  | duplicateMemoryMap
  | badEntrySize
  | unsupportedEntryVersion
  | tooManyEntries
  | nonzeroEntryReserved
  | zeroLengthEntry
  | entryAddressOverflow
  | typedHandoffRejected (reason : BootMemoryMap.Error)
  | internalBounds
  deriving BEq, DecidableEq, Repr

private def readByte (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  match bytes[offset]? with
  | none => .error .truncatedField
  | some byte => .ok byte.toNat

private def readLEAux (bytes : List UInt8) (offset remaining factor acc : Nat) :
    Except Error Nat :=
  match remaining with
  | 0 => .ok acc
  | remaining + 1 => do
      let byte ← readByte bytes offset
      readLEAux bytes (offset + 1) remaining (factor * 256) (acc + byte * factor)

def readLE (bytes : List UInt8) (offset width : Nat) : Except Error Nat :=
  readLEAux bytes offset width 1 0

def readU32 (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  readLE bytes offset 4

def readU64 (bytes : List UInt8) (offset : Nat) : Except Error Nat :=
  readLE bytes offset 8

def low32Nat (word : Nat) : Nat := word % (2 ^ 32)
def high32Nat (word : Nat) : Nat := word / (2 ^ 32)

namespace AcpiRootDecoder

open LeanOS.BootTopology

inductive Error where
  | handoffRejected (reason : BootMemoryMapDecoder.Error)
  | truncatedTag
  | malformedTagSize
  | tagOutOfBounds
  | missingEndTag
  | misplacedEndTag
  | tooManyTags
  | invalidSignature
  | unsupportedRevision
  | invalidRsdpLength
  | invalidLegacyChecksum
  | invalidExtendedChecksum
  deriving BEq, DecidableEq, Repr

private def rsdpSignature : List UInt8 :=
  [0x52, 0x53, 0x44, 0x20, 0x50, 0x54, 0x52, 0x20]

private def checksum (bytes : List UInt8) (offset length : Nat) : Nat :=
  ((bytes.drop offset).take length).foldl
    (fun total byte => (total + byte.toNat) % 256) 0

private def decodeRootTag (bytes : List UInt8) (offset tagType tagSize : Nat) :
    Except Error RawAcpiRootTag := do
  let payloadOffset := offset + 8
  let payloadSize := tagSize - 8
  if (bytes.drop payloadOffset).take 8 != rsdpSignature then
    throw .invalidSignature
  if payloadSize < 20 then throw .invalidRsdpLength
  if checksum bytes payloadOffset 20 != 0 then throw .invalidLegacyChecksum
  let revision ← match bytes[payloadOffset + 15]? with
    | some byte => pure byte.toNat
    | none => throw .truncatedTag
  let rsdtAddress ← match readU32 bytes (payloadOffset + 16) with
    | .ok value => pure value
    | .error _ => throw .truncatedTag
  let legacy : AcpiLegacyRoot :=
    { oemId := (bytes.drop (payloadOffset + 9)).take 6
      rsdtAddress := UInt32.ofNat rsdtAddress }
  if tagType == 14 then
    if tagSize != 28 || payloadSize != 20 then throw .invalidRsdpLength
    if revision != 0 then throw .unsupportedRevision
    pure (.old legacy)
  else
    if tagSize < 44 || payloadSize < 36 then throw .invalidRsdpLength
    if revision < 2 then throw .unsupportedRevision
    let declaredLength ← match readU32 bytes (payloadOffset + 20) with
      | .ok value => pure value
      | .error _ => throw .truncatedTag
    if declaredLength != 36 || payloadSize != declaredLength then
      throw .invalidRsdpLength
    if checksum bytes payloadOffset declaredLength != 0 then
      throw .invalidExtendedChecksum
    let xsdtAddress ← match readU64 bytes (payloadOffset + 24) with
      | .ok value => pure value
      | .error _ => throw .truncatedTag
    pure (.new legacy (UInt64.ofNat xsdtAddress))

private def scan (bytes : List UInt8) (total offset fuel : Nat)
    (rootsRev : List RawAcpiRootTag) : Except Error (List RawAcpiRootTag) := do
  if offset == total then throw .missingEndTag
  match fuel with
  | 0 => throw .tooManyTags
  | fuel + 1 =>
      if offset + 8 > total then throw .truncatedTag
      let tagWord ← match readU64 bytes offset with
        | .ok value => pure value
        | .error _ => throw .truncatedTag
      let tagType := low32Nat tagWord
      let tagSize := high32Nat tagWord
      if tagSize < 8 then throw .malformedTagSize
      if offset + tagSize > total then throw .tagOutOfBounds
      let advance := aligned8 tagSize
      if offset + advance > total then throw .tagOutOfBounds
      if tagType == 0 then
        if tagSize != 8 then throw .malformedTagSize
        if offset + advance != total then throw .misplacedEndTag
        pure rootsRev.reverse
      else if tagType == 14 || tagType == 15 then
        let root ← decodeRootTag bytes offset tagType tagSize
        scan bytes total (offset + advance) fuel (root :: rootsRev)
      else
        scan bytes total (offset + advance) fuel rootsRev

end AcpiRootDecoder

private theorem readLEAux_drop (bytes : List UInt8)
    (offset remaining factor acc : Nat) :
    readLEAux (bytes.drop offset) 0 remaining factor acc =
      readLEAux bytes offset remaining factor acc := by
  induction remaining generalizing bytes offset factor acc with
  | zero =>
      rfl
  | succ remaining ih =>
      simp only [readLEAux]
      have hbyte :
          readByte (bytes.drop offset) 0 = readByte bytes offset := by
        simp [readByte, List.getElem?_drop]
      rw [hbyte]
      cases hread : readByte bytes offset with
      | error reason =>
          rfl
      | ok byte =>
          simp only [bind, Except.bind]
          rw [← ih bytes (offset + 1) (factor * 256) (acc + byte * factor)]
          rw [← ih (bytes.drop offset) 1 (factor * 256) (acc + byte * factor)]
          simp [List.drop_drop]

private theorem readLEAux_take (bytes : List UInt8)
    (remaining factor acc : Nat) :
    readLEAux (bytes.take remaining) 0 remaining factor acc =
      readLEAux bytes 0 remaining factor acc := by
  induction remaining generalizing bytes factor acc with
  | zero =>
      rfl
  | succ remaining ih =>
      cases bytes with
      | nil =>
          simp [readLEAux, readByte]
      | cons byte bytes =>
          simp only [List.take_succ_cons, readLEAux]
          simp only [readByte, List.getElem?_cons_zero, bind, Except.bind]
          rw [← readLEAux_drop (byte :: bytes.take remaining) 1
            remaining (factor * 256) (acc + byte.toNat * factor)]
          rw [← readLEAux_drop (byte :: bytes) 1
            remaining (factor * 256) (acc + byte.toNat * factor)]
          simp only [List.drop_succ_cons]
          exact ih bytes (factor * 256) (acc + byte.toNat * factor)

/-- Reading a fixed-width little-endian field is unchanged by first isolating
the exact source slice.  Canonical scalar chunks use the left side, while the
rich decoder uses the right side. -/
theorem readLE_drop_take (bytes : List UInt8) (offset width : Nat) :
    readLE ((bytes.drop offset).take width) 0 width =
      readLE bytes offset width := by
  unfold readLE
  rw [readLEAux_take, readLEAux_drop]

/-- Every aligned canonical chunk is read as the same 64-bit word by the rich
decoder at its source offset and by the scalar replay from the isolated chunk. -/
theorem readU64_drop_take (bytes : List UInt8) (offset : Nat) :
    readU64 ((bytes.drop offset).take 8) 0 = readU64 bytes offset := by
  exact readLE_drop_take bytes offset 8

/-- The scalar low-half operation and the rich decoder's Nat projection agree
for every admitted 64-bit word. -/
theorem low32Word_ofNat (word : Nat) (hword : word < wordLimit) :
    UInt64.ofNat word &&& 0xffffffff =
      UInt64.ofNat (low32Nat word) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_and, UInt64.toNat_ofNat_of_lt' hword]
  have hlow : low32Nat word < UInt64.size := by
    unfold low32Nat UInt64.size
    omega
  rw [UInt64.toNat_ofNat_of_lt' hlow]
  change word &&& (2 ^ 32 - 1) = word % (2 ^ 32)
  exact Nat.and_two_pow_sub_one_eq_mod word 32

/-- The scalar high-half operation and the rich decoder's Nat projection
agree for every admitted 64-bit word. -/
theorem high32Word_ofNat (word : Nat) (hword : word < wordLimit) :
    UInt64.ofNat word >>> 32 =
      UInt64.ofNat (high32Nat word) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' hword]
  have hhigh : high32Nat word < UInt64.size := by
    unfold high32Nat UInt64.size
    unfold wordLimit at hword
    omega
  rw [UInt64.toNat_ofNat_of_lt' hhigh]
  simp [Nat.shiftRight_eq_div_pow, high32Nat]

private theorem readByte_lt_byteLimit
    (bytes : List UInt8) (offset byte : Nat)
    (hread : readByte bytes offset = .ok byte) :
    byte < 256 := by
  unfold readByte at hread
  cases hbyte : bytes[offset]? with
  | none =>
      rw [hbyte] at hread
      contradiction
  | some source =>
      rw [hbyte] at hread
      injection hread with heq
      subst byte
      exact source.toNat_lt

private theorem readLEAux_lt_factor
    (bytes : List UInt8) (offset remaining factor acc value : Nat)
    (hacc : acc < factor)
    (hread : readLEAux bytes offset remaining factor acc = .ok value) :
    value < factor * 256 ^ remaining := by
  induction remaining generalizing offset factor acc with
  | zero =>
      simp only [readLEAux] at hread
      injection hread with heq
      subst value
      simpa using hacc
  | succ remaining ih =>
      simp only [readLEAux, bind, Except.bind] at hread
      cases hbyte : readByte bytes offset with
      | error reason =>
          rw [hbyte] at hread
          contradiction
      | ok byte =>
          rw [hbyte] at hread
          have hbyteLt := readByte_lt_byteLimit bytes offset byte hbyte
          have hnextAcc : acc + byte * factor < factor * 256 := by
            calc
              acc + byte * factor < factor + byte * factor :=
                Nat.add_lt_add_right hacc (byte * factor)
              _ = (byte + 1) * factor := by
                simp [Nat.add_mul, Nat.add_comm]
              _ ≤ 256 * factor :=
                Nat.mul_le_mul_right factor (by omega)
              _ = factor * 256 := Nat.mul_comm _ _
          have hnext :=
            ih (offset + 1) (factor * 256) (acc + byte * factor)
              hnextAcc hread
          rw [Nat.pow_succ]
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnext

/-- Every successful checked eight-byte read is representable without
truncation in the scalar decoder's `UInt64` word. -/
theorem readU64_lt_wordLimit
    (bytes : List UInt8) (offset value : Nat)
    (hread : readU64 bytes offset = .ok value) :
    value < wordLimit := by
  have hbound :=
    readLEAux_lt_factor bytes offset 8 1 0 value (by decide) hread
  simpa [readU64, readLE, wordLimit] using hbound

private theorem readLEAux_succeeds (bytes : List UInt8)
    (offset remaining factor acc : Nat)
    (hbound : offset + remaining ≤ bytes.length) :
    ∃ value, readLEAux bytes offset remaining factor acc = .ok value := by
  induction remaining generalizing offset factor acc with
  | zero =>
      simp [readLEAux]
  | succ remaining ih =>
      have hoffset : offset < bytes.length := by omega
      rw [readLEAux]
      unfold readByte
      rw [List.getElem?_eq_getElem hoffset]
      apply ih
      omega

/-- An eight-byte chunk is sufficient for the decoder's checked scalar read.
This is the byte-side precondition used by the stream replay refinement; it
does not assume any particular byte values. -/
theorem readU64_succeeds_of_length (bytes : List UInt8)
    (hlength : 8 ≤ bytes.length) :
    ∃ value, readU64 bytes 0 = .ok value := by
  exact readLEAux_succeeds bytes 0 8 1 0 hlength

def memoryKind (kind : Nat) : MemoryKind :=
  match kind with
  | 1 => .usable
  | 3 => .acpiReclaimable
  | 4 => .acpiNvs
  | 5 => .badMemory
  | _ => .reserved

/-- The scalar raw entry type word and rich typed classification have one
usable case: Multiboot type one. -/
theorem memoryKind_usable_word (kind : Nat) :
    (memoryKind kind == MemoryKind.usable) = (kind == 1) := by
  unfold memoryKind
  split <;> try rfl
  next hkind _ _ _ =>
    have heq : (kind == 1) = false := by
      exact beq_false_of_ne hkind
    rw [heq]
    rfl

private def decodeEntries (bytes : List UInt8) (offset count : Nat) :
    Except Error (List RawEntry) :=
  match count with
  | 0 => .ok []
  | count + 1 => do
      let base ← readU64 bytes offset
      let length ← readU64 bytes (offset + 8)
      let kindWord ← readU64 bytes (offset + 16)
      let kind := low32Nat kindWord
      let reserved := high32Nat kindWord
      if reserved != 0 then throw .nonzeroEntryReserved
      if length == 0 then throw .zeroLengthEntry
      if base ≥ wordLimit || length ≥ wordLimit ||
          length ≥ wordLimit - base then throw .entryAddressOverflow
      let rest ← decodeEntries bytes (offset + memoryMapEntrySize) count
      pure ({ base, length, kind := memoryKind kind } :: rest)

/-- Structural evidence for every entry returned by the recursive rich
decoder.  Each constructor retains the exact three source words and the
admission checks that made the entry acceptable.  This is the entry-level
induction principle used when relating the rich traversal to canonical
eight-byte scalar chunks. -/
inductive SuccessfulEntryDecodeTraversal (bytes : List UInt8) :
    Nat → Nat → List RawEntry → Prop
  | done (offset : Nat) :
      SuccessfulEntryDecodeTraversal bytes offset 0 []
  | entry (offset count base length kindWord : Nat) (rest : List RawEntry)
      (hbase : readU64 bytes offset = .ok base)
      (hlength : readU64 bytes (offset + 8) = .ok length)
      (hkindWord : readU64 bytes (offset + 16) = .ok kindWord)
      (hreserved : high32Nat kindWord = 0)
      (hlengthNonzero : length ≠ 0)
      (hbaseBound : base < wordLimit)
      (hlengthBound : length < wordLimit)
      (hstopBound : length < wordLimit - base)
      (hrest :
        SuccessfulEntryDecodeTraversal bytes
          (offset + memoryMapEntrySize) count rest) :
      SuccessfulEntryDecodeTraversal bytes offset (count + 1)
        ({ base, length, kind := memoryKind (low32Nat kindWord) } :: rest)

/-- Every successful recursive entry decode constructs the exact structural
entry witness.  No typed entry supplied by a caller can satisfy this theorem
without the corresponding checked source words. -/
private theorem decodeEntries_constructs_traversal
    (bytes : List UInt8) (offset count : Nat) (entries : List RawEntry)
    (hdecode : decodeEntries bytes offset count = .ok entries) :
    SuccessfulEntryDecodeTraversal bytes offset count entries := by
  induction count generalizing offset entries with
  | zero =>
      simp [decodeEntries] at hdecode
      subst entries
      exact .done offset
  | succ count ih =>
      unfold decodeEntries at hdecode
      simp only [bind, Except.bind] at hdecode
      cases hbase : readU64 bytes offset with
      | error reason =>
          simp only [hbase] at hdecode
          contradiction
      | ok base =>
          simp only [hbase] at hdecode
          cases hlength : readU64 bytes (offset + 8) with
          | error reason =>
              simp only [hlength] at hdecode
              contradiction
          | ok length =>
              simp only [hlength] at hdecode
              cases hkindWord : readU64 bytes (offset + 16) with
              | error reason =>
                  simp only [hkindWord] at hdecode
                  contradiction
              | ok kindWord =>
                  simp only [hkindWord] at hdecode
                  by_cases hreserved : high32Nat kindWord != 0
                  · rw [if_pos hreserved] at hdecode
                    contradiction
                  · rw [if_neg hreserved] at hdecode
                    by_cases hzero : length == 0
                    · rw [if_pos hzero] at hdecode
                      contradiction
                    · rw [if_neg hzero] at hdecode
                      by_cases hoverflow :
                          base ≥ wordLimit || length ≥ wordLimit ||
                            length ≥ wordLimit - base
                      · rw [if_pos hoverflow] at hdecode
                        contradiction
                      · rw [if_neg hoverflow] at hdecode
                        cases hrest :
                            decodeEntries bytes
                              (offset + memoryMapEntrySize) count with
                        | error reason =>
                            simp only [hrest] at hdecode
                            contradiction
                        | ok rest =>
                            simp only [hrest] at hdecode
                            injection hdecode with hentries
                            subst entries
                            apply SuccessfulEntryDecodeTraversal.entry
                              offset count base length kindWord rest
                              hbase hlength hkindWord
                            · simpa using hreserved
                            · simpa using hzero
                            · simp at hoverflow
                              omega
                            · simp at hoverflow
                              omega
                            · simp at hoverflow
                              omega
                            · exact ih (offset + memoryMapEntrySize) rest hrest

private def decodeTags (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev : List Tag) : Except Error (List Tag) := do
  if offset == total then throw .missingEndTag
  match fuel with
  | 0 => throw .tooManyTags
  | fuel + 1 =>
      if offset + 8 > total then throw .truncatedField
      let tagWord ← readU64 bytes offset
      let tagType := low32Nat tagWord
      let tagSize := high32Nat tagWord
      if tagSize < 8 then throw .malformedTagSize
      if offset + tagSize > total then throw .tagOutOfBounds
      let advance := aligned8 tagSize
      if offset + advance > total then throw .tagOutOfBounds
      if tagType == 0 then
        if tagSize != 8 then throw .malformedTagSize
        if offset + advance != total then throw .misplacedEndTag
        if !sawMemoryMap then throw .missingMemoryMap
        pure (tagsRev.reverse ++ [.end 8])
      else if tagType == 6 then
        if sawMemoryMap then throw .duplicateMemoryMap
        if tagSize < memoryMapTagHeaderSize then throw .malformedTagSize
        let layoutWord ← readU64 bytes (offset + 8)
        let entrySize := low32Nat layoutWord
        let entryVersion := high32Nat layoutWord
        if entrySize != memoryMapEntrySize then throw .badEntrySize
        if entryVersion != 0 then throw .unsupportedEntryVersion
        let entryBytes := tagSize - memoryMapTagHeaderSize
        if entryBytes % entrySize != 0 then throw .malformedTagSize
        let entryCount := entryBytes / entrySize
        if entryCount > maxEntries then throw .tooManyEntries
        let entries ← decodeEntries bytes (offset + memoryMapTagHeaderSize) entryCount
        decodeTags bytes total (offset + advance) fuel true
          (.memoryMap tagSize entrySize entryVersion entries :: tagsRev)
      else
        decodeTags bytes total (offset + advance) fuel sawMemoryMap
          (.ignored tagSize :: tagsRev)

/-- Structural evidence for every tag consumed by a successful recursive byte
walk.  Each constructor retains the exact source header word and all arithmetic
that admitted its aligned advance.  A memory-map constructor additionally
retains its layout word and the exact entry-level source traversal.  This
proof-only relation is the tag-level induction principle needed to align the
rich decoder with canonical eight-byte scalar chunks. -/
inductive SuccessfulTagDecodeTraversal (bytes : List UInt8) (total : Nat) :
    Nat → Nat → Bool → List Tag → List Tag → Prop
  | endTag (offset fuel tagWord : Nat) (tagsRev : List Tag)
      (hread : readU64 bytes offset = .ok tagWord)
      (htype : low32Nat tagWord = 0)
      (hsize : high32Nat tagWord = 8)
      (hend : offset + 8 = total) :
      SuccessfulTagDecodeTraversal bytes total offset (fuel + 1) true tagsRev
        (tagsRev.reverse ++ [.end 8])
  | ignoredTag (offset fuel tagWord : Nat) (sawMemoryMap : Bool)
      (tagsRev tags : List Tag)
      (hread : readU64 bytes offset = .ok tagWord)
      (hsize : 8 ≤ high32Nat tagWord)
      (hcontent : offset + high32Nat tagWord ≤ total)
      (hadvance : offset + aligned8 (high32Nat tagWord) ≤ total)
      (htypeEnd : low32Nat tagWord ≠ 0)
      (htypeMap : low32Nat tagWord ≠ 6)
      (hrest :
        SuccessfulTagDecodeTraversal bytes total
          (offset + aligned8 (high32Nat tagWord)) fuel sawMemoryMap
          (.ignored (high32Nat tagWord) :: tagsRev) tags) :
      SuccessfulTagDecodeTraversal bytes total offset (fuel + 1) sawMemoryMap
        tagsRev tags
  | memoryMapTag (offset fuel tagWord layoutWord : Nat)
      (tagsRev tags : List Tag) (entries : List RawEntry)
      (hread : readU64 bytes offset = .ok tagWord)
      (hsize : memoryMapTagHeaderSize ≤ high32Nat tagWord)
      (hcontent : offset + high32Nat tagWord ≤ total)
      (hadvance : offset + aligned8 (high32Nat tagWord) ≤ total)
      (htype : low32Nat tagWord = 6)
      (hlayout : readU64 bytes (offset + 8) = .ok layoutWord)
      (hentrySize : low32Nat layoutWord = memoryMapEntrySize)
      (hentryVersion : high32Nat layoutWord = 0)
      (halignedEntries :
        (high32Nat tagWord - memoryMapTagHeaderSize) % memoryMapEntrySize = 0)
      (hentryBound :
        (high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize ≤
          maxEntries)
      (hentries :
        SuccessfulEntryDecodeTraversal bytes
          (offset + memoryMapTagHeaderSize)
          ((high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize)
          entries)
      (hrest :
        SuccessfulTagDecodeTraversal bytes total
          (offset + aligned8 (high32Nat tagWord)) fuel true
          (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
            (high32Nat layoutWord) entries :: tagsRev) tags) :
      SuccessfulTagDecodeTraversal bytes total offset (fuel + 1) false tagsRev tags

/-- The entry traversal consumes exactly the number of entries carried by its
index.  This small structural fact is needed when the tag-level certificate is
converted from byte counts to the typed memory-map list. -/
theorem successfulEntryDecodeTraversal_length
    (bytes : List UInt8) (offset count : Nat) (entries : List RawEntry)
    (h : SuccessfulEntryDecodeTraversal bytes offset count entries) :
    entries.length = count := by
  induction h with
  | done =>
      rfl
  | entry =>
      simp_all

/-- Every successful tag traversal starts at a complete source header strictly
before the advertised terminal extent.  This supplies the local byte bound
needed to select the corresponding canonical eight-byte scalar chunk at each
tag-phase induction step. -/
theorem successfulTagDecodeTraversal_offset_lt_total
    (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag)
    (h :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap tagsRev tags) :
    offset + 8 ≤ total := by
  induction h with
  | endTag offset fuel tagWord tagsRev hread htype hsize hend =>
      omega
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest ih =>
      unfold aligned8 at ih
      omega
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentries hrest ih =>
      unfold aligned8 at ih
      omega

/-- After the unique memory-map tag has been seen, a successful traversal can
consume only ignored tags before the terminal end tag.  The exact ignored-tag
sizes are retained so the source order can subsequently be reconstructed. -/
theorem successfulTagDecodeTraversal_afterMap_shape
    (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag)
    (hsaw : sawMemoryMap = true)
    (h :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap tagsRev tags) :
    ∃ ignoredSizes : List Nat,
      tags =
        tagsRev.reverse ++ ignoredSizes.map Tag.ignored ++ [.end 8] := by
  induction h with
  | endTag =>
      exact ⟨[], by simp⟩
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags _ _ _ _ _ _
      hrest ih =>
      subst sawMemoryMap
      obtain ⟨ignoredSizes, hshape⟩ := ih rfl
      refine ⟨high32Nat tagWord :: ignoredSizes, ?_⟩
      rw [hshape]
      simp
  | memoryMapTag =>
      contradiction

/-- Ignored tags on either side of one well-shaped memory-map tag do not
change the typed entry list extracted from that tag. -/
theorem extractMemoryMap_ignored_around
    (beforeSizes afterSizes : List Nat) (size : Nat) (entries : List RawEntry)
    (hsize : size = memoryMapTagHeaderSize + memoryMapEntrySize * entries.length)
    (hbound : entries.length ≤ maxEntries) :
    extractMemoryMap
        (beforeSizes.map Tag.ignored ++
          [.memoryMap size memoryMapEntrySize 0 entries] ++
          afterSizes.map Tag.ignored ++ [.end 8]) =
      .ok entries := by
  have hlast :
      (afterSizes.map Tag.ignored ++ [Tag.end 8]).getLast? =
        some (Tag.end 8) := by
    simp [List.getLast?_append]
  have hdrop :
      (afterSizes.map Tag.ignored ++ [Tag.end 8]).dropLast =
        afterSizes.map Tag.ignored := by
    induction afterSizes with
    | nil =>
        rfl
    | cons afterHead afterTail ih =>
        cases afterTail <;> simp [List.dropLast]
  induction beforeSizes with
  | nil =>
      simp only [List.map_nil, List.nil_append, List.singleton_append]
      cases afterSizes with
      | nil =>
          simp [extractMemoryMap.eq_4, hsize, memoryMapTagHeaderSize,
            memoryMapEntrySize, hbound]
      | cons afterHead afterTail =>
          simp only [List.map_cons, List.cons_append] at hlast hdrop ⊢
          rw [extractMemoryMap.eq_6 _ _ _ _ _
            (by intro endSize heq; cases heq) (by simp)]
          have hnotTooMany : ¬entries.length > maxEntries := by omega
          simp [hsize, memoryMapTagHeaderSize, memoryMapEntrySize,
            hnotTooMany, hlast, show
              (some (Tag.end 8) != some (Tag.end 8)) = false by decide,
            hdrop]
  | cons prefixHead prefixTail ih =>
      simpa [extractMemoryMap] using ih

/-- Starting before the unique memory-map tag with only ignored tags already
accumulated, every successful tag traversal exposes the exact entry-level
source certificate for the list returned by typed tag extraction.  This is the
tag/entry induction bridge required before constructing the scalar traversal
over canonical chunks. -/
private theorem successfulTagDecodeTraversal_extracts_entry_traversal_aux
    (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag)
    (hsaw : sawMemoryMap = false)
    (h :
      SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap tagsRev tags)
    (beforeSizes : List Nat)
    (hprefix : tagsRev.reverse = beforeSizes.map Tag.ignored) :
    ∃ entryOffset entryCount entries,
      SuccessfulEntryDecodeTraversal bytes entryOffset entryCount entries ∧
      extractMemoryMap tags = .ok entries := by
  induction h generalizing beforeSizes with
  | ignoredTag offset fuel tagWord sawMemoryMap tagsRev tags hread hsize
      hcontent hadvance htypeEnd htypeMap hrest ih =>
      subst sawMemoryMap
      exact ih rfl (beforeSizes ++ [high32Nat tagWord]) (by simp [hprefix])
  | memoryMapTag offset fuel tagWord layoutWord tagsRev tags entries hread
      hsize hcontent hadvance htype hlayout hentrySize hentryVersion
      halignedEntries hentryBound hentries hrest =>
      obtain ⟨afterSizes, hshape⟩ :=
        successfulTagDecodeTraversal_afterMap_shape
          bytes total
          (offset + aligned8 (high32Nat tagWord)) fuel
          true
          (.memoryMap (high32Nat tagWord) (low32Nat layoutWord)
            (high32Nat layoutWord) entries :: tagsRev)
          tags rfl hrest
      have hlength :=
        successfulEntryDecodeTraversal_length bytes
          (offset + memoryMapTagHeaderSize)
          ((high32Nat tagWord - memoryMapTagHeaderSize) /
            memoryMapEntrySize)
          entries hentries
      have htagSize :
          high32Nat tagWord =
            memoryMapTagHeaderSize + memoryMapEntrySize * entries.length := by
        have hdiv :=
          Nat.mod_add_div
            (high32Nat tagWord - memoryMapTagHeaderSize)
            memoryMapEntrySize
        rw [halignedEntries, Nat.zero_add, ← hlength] at hdiv
        omega
      refine ⟨offset + memoryMapTagHeaderSize,
        (high32Nat tagWord - memoryMapTagHeaderSize) / memoryMapEntrySize,
        entries, hentries, ?_⟩
      rw [hshape]
      simp only [List.reverse_cons, List.append_assoc]
      rw [hprefix, hentrySize, hentryVersion]
      simpa only [List.append_assoc] using
        extractMemoryMap_ignored_around beforeSizes afterSizes
          (high32Nat tagWord) entries htagSize (by
            rw [hlength]
            exact hentryBound)
  | endTag =>
      contradiction

/-- Starting before the unique memory-map tag with only ignored tags already
accumulated, every successful tag traversal exposes the exact entry-level
source certificate for the list returned by typed tag extraction. -/
theorem successfulTagDecodeTraversal_extracts_entry_traversal
    (bytes : List UInt8) (total offset fuel : Nat)
    (tagsRev tags : List Tag)
    (h :
      SuccessfulTagDecodeTraversal bytes total offset fuel false tagsRev tags)
    (beforeSizes : List Nat)
    (hprefix : tagsRev.reverse = beforeSizes.map Tag.ignored) :
    ∃ entryOffset entryCount entries,
      SuccessfulEntryDecodeTraversal bytes entryOffset entryCount entries ∧
      extractMemoryMap tags = .ok entries :=
  successfulTagDecodeTraversal_extracts_entry_traversal_aux
    bytes total offset fuel false tagsRev tags rfl h beforeSizes hprefix

/-- Every successful recursive tag decode constructs the exact tag/source
traversal certificate.  The proof follows the decoder's fuel recursion and
therefore introduces no second parser or acceptance assumption. -/
private theorem decodeTags_constructs_traversal
    (bytes : List UInt8) (total offset fuel : Nat)
    (sawMemoryMap : Bool) (tagsRev tags : List Tag)
    (hdecode :
      decodeTags bytes total offset fuel sawMemoryMap tagsRev = .ok tags) :
    SuccessfulTagDecodeTraversal bytes total offset fuel sawMemoryMap tagsRev tags := by
  induction fuel generalizing offset sawMemoryMap tagsRev tags with
  | zero =>
      unfold decodeTags at hdecode
      by_cases hoffset : offset == total
      · rw [if_pos hoffset] at hdecode
        contradiction
      · rw [if_neg hoffset] at hdecode
        contradiction
  | succ fuel ih =>
      unfold decodeTags at hdecode
      simp only [bind, Except.bind] at hdecode
      by_cases hoffset : offset == total
      · rw [if_pos hoffset] at hdecode
        contradiction
      · rw [if_neg hoffset] at hdecode
        by_cases hheader : offset + 8 > total
        · rw [if_pos hheader] at hdecode
          contradiction
        · rw [if_neg hheader] at hdecode
          cases htagWord : readU64 bytes offset with
          | error reason =>
              simp only [htagWord] at hdecode
              contradiction
          | ok tagWord =>
              simp only [htagWord] at hdecode
              by_cases hsize : high32Nat tagWord < 8
              · rw [if_pos hsize] at hdecode
                contradiction
              · rw [if_neg hsize] at hdecode
                by_cases hcontent : offset + high32Nat tagWord > total
                · rw [if_pos hcontent] at hdecode
                  contradiction
                · rw [if_neg hcontent] at hdecode
                  by_cases hadvance :
                      offset + aligned8 (high32Nat tagWord) > total
                  · rw [if_pos hadvance] at hdecode
                    contradiction
                  · rw [if_neg hadvance] at hdecode
                    by_cases hend : low32Nat tagWord == 0
                    · rw [if_pos hend] at hdecode
                      by_cases hendSize : high32Nat tagWord != 8
                      · rw [if_pos hendSize] at hdecode
                        contradiction
                      · rw [if_neg hendSize] at hdecode
                        by_cases hendOffset :
                            offset + aligned8 (high32Nat tagWord) != total
                        · rw [if_pos hendOffset] at hdecode
                          contradiction
                        · rw [if_neg hendOffset] at hdecode
                          by_cases hsaw : !sawMemoryMap
                          · rw [if_pos hsaw] at hdecode
                            contradiction
                          · rw [if_neg hsaw] at hdecode
                            injection hdecode with htags
                            subst tags
                            have hsawTrue : sawMemoryMap = true := by
                              simpa using hsaw
                            subst sawMemoryMap
                            apply SuccessfulTagDecodeTraversal.endTag
                              offset fuel tagWord tagsRev htagWord
                            · simpa using hend
                            · simpa using hendSize
                            · have hsizeEq : high32Nat tagWord = 8 := by
                                simpa using hendSize
                              have haligned :
                                  aligned8 (high32Nat tagWord) = 8 := by
                                simp [hsizeEq, aligned8]
                              rw [haligned] at hendOffset
                              simpa using hendOffset
                    · rw [if_neg hend] at hdecode
                      by_cases hmap : low32Nat tagWord == 6
                      · rw [if_pos hmap] at hdecode
                        by_cases hsaw : sawMemoryMap
                        · rw [if_pos hsaw] at hdecode
                          contradiction
                        · rw [if_neg hsaw] at hdecode
                          by_cases hmapSize :
                              high32Nat tagWord < memoryMapTagHeaderSize
                          · rw [if_pos hmapSize] at hdecode
                            contradiction
                          · rw [if_neg hmapSize] at hdecode
                            cases hlayout :
                                readU64 bytes (offset + 8) with
                            | error reason =>
                                simp only [hlayout] at hdecode
                                contradiction
                            | ok layoutWord =>
                                simp only [hlayout] at hdecode
                                by_cases hentrySize :
                                    low32Nat layoutWord != memoryMapEntrySize
                                · rw [if_pos hentrySize] at hdecode
                                  contradiction
                                · rw [if_neg hentrySize] at hdecode
                                  by_cases hentryVersion :
                                      high32Nat layoutWord != 0
                                  · rw [if_pos hentryVersion] at hdecode
                                    contradiction
                                  · rw [if_neg hentryVersion] at hdecode
                                    by_cases hentryAlignment :
                                        (high32Nat tagWord -
                                            memoryMapTagHeaderSize) %
                                            low32Nat layoutWord != 0
                                    · rw [if_pos hentryAlignment] at hdecode
                                      contradiction
                                    · rw [if_neg hentryAlignment] at hdecode
                                      by_cases hentryCount :
                                          (high32Nat tagWord -
                                              memoryMapTagHeaderSize) /
                                              low32Nat layoutWord > maxEntries
                                      · rw [if_pos hentryCount] at hdecode
                                        contradiction
                                      · rw [if_neg hentryCount] at hdecode
                                        have hsawFalse : sawMemoryMap = false := by
                                          simpa using hsaw
                                        subst sawMemoryMap
                                        have hentrySizeEq :
                                            low32Nat layoutWord =
                                              memoryMapEntrySize := by
                                          simpa using hentrySize
                                        have hentryVersionEq :
                                            high32Nat layoutWord = 0 := by
                                          simpa using hentryVersion
                                        cases hdecodedEntries :
                                            decodeEntries bytes
                                              (offset + memoryMapTagHeaderSize)
                                              ((high32Nat tagWord -
                                                memoryMapTagHeaderSize) /
                                                low32Nat layoutWord) with
                                        | error reason =>
                                            simp only [hdecodedEntries] at hdecode
                                            contradiction
                                        | ok entries =>
                                            simp only [hdecodedEntries] at hdecode
                                            apply
                                              SuccessfulTagDecodeTraversal.memoryMapTag
                                                offset fuel tagWord layoutWord
                                                tagsRev tags entries htagWord
                                            · simpa using hmapSize
                                            · simpa using hcontent
                                            · simpa using hadvance
                                            · simpa using hmap
                                            · exact hlayout
                                            · exact hentrySizeEq
                                            · exact hentryVersionEq
                                            · simpa [hentrySizeEq] using hentryAlignment
                                            · simpa [hentrySizeEq] using hentryCount
                                            · simpa [hentrySizeEq] using
                                                decodeEntries_constructs_traversal
                                                  bytes
                                                  (offset + memoryMapTagHeaderSize)
                                                  ((high32Nat tagWord -
                                                    memoryMapTagHeaderSize) /
                                                    low32Nat layoutWord)
                                                  entries hdecodedEntries
                                            · exact ih
                                                (offset +
                                                  aligned8 (high32Nat tagWord))
                                                true
                                                (.memoryMap (high32Nat tagWord)
                                                  (low32Nat layoutWord)
                                                  (high32Nat layoutWord) entries ::
                                                  tagsRev)
                                                tags hdecode
                      · rw [if_neg hmap] at hdecode
                        apply SuccessfulTagDecodeTraversal.ignoredTag
                          offset fuel tagWord sawMemoryMap tagsRev tags htagWord
                        · simpa using hsize
                        · simpa using hcontent
                        · simpa using hadvance
                        · simpa using hend
                        · simpa using hmap
                        · exact ih
                            (offset + aligned8 (high32Nat tagWord))
                            sawMemoryMap
                            (.ignored (high32Nat tagWord) :: tagsRev)
                            tags hdecode

def withinBounds (handoff : Handoff) (entries : List RawEntry) : Bool :=
  handoff.totalSize ≤ maxTagBytes &&
    handoff.tags.length ≤ maxTags &&
    entries.length ≤ maxEntries

structure Decoded where
  handoff : Handoff
  entries : List RawEntry
  handoffValid : validateHandoff handoff = .ok entries
  entriesValid : validateEntries entries = .ok ()
  bounds : withinBounds handoff entries = true
  infoAddressAtLeastPage : pageBytes ≤ handoff.infoAddress

/-- Kernel-checked evidence that one successful rich result came from the
recursive byte traversal, rather than from caller-supplied typed fields.  The
certificate retains the exact information-header word, the exact tag list
returned by `decodeTags`, and the validation/bounds equations carried by the
public result.  It is proof-side evidence only and is erased by code
generation. -/
structure SuccessfulRichDecodeTraversal (input : Input) (decoded : Decoded) : Prop where
  traversed :
    ∃ infoWord tags,
      readU64 input.bytes 0 = .ok infoWord ∧
      low32Nat infoWord = input.bytes.length ∧
      high32Nat infoWord = 0 ∧
      decodeTags input.bytes (low32Nat infoWord) 8 maxTags false [] = .ok tags ∧
      SuccessfulTagDecodeTraversal input.bytes (low32Nat infoWord)
        8 maxTags false [] tags ∧
      decoded.handoff =
        { magic := input.magic
          infoAddress := input.infoAddress
          totalSize := low32Nat infoWord
          tags } ∧
      validateHandoff decoded.handoff = .ok decoded.entries ∧
      validateEntries decoded.entries = .ok () ∧
      withinBounds decoded.handoff decoded.entries = true

/-- A retained successful rich traversal binds the unique memory-map entry
walk to exactly `decoded.entries`, not merely to an existential list decoded
somewhere in the tag stream.  The proof first extracts the source walk from
the tag induction above and then uses the already-retained typed handoff
validation equation to identify its result. -/
theorem successfulRichDecodeTraversal_entries_source
    (input : Input) (decoded : Decoded)
    (h : SuccessfulRichDecodeTraversal input decoded) :
    ∃ entryOffset entryCount,
      SuccessfulEntryDecodeTraversal input.bytes entryOffset entryCount
        decoded.entries := by
  obtain ⟨infoWord, tags, hinfo, htotal, hreserved, htags, htraversal, hhandoff,
    hvalid, hentries, hbounds⟩ := h.traversed
  obtain ⟨entryOffset, entryCount, sourceEntries, hsource, hextract⟩ :=
    successfulTagDecodeTraversal_extracts_entry_traversal
      input.bytes (low32Nat infoWord) 8 maxTags [] tags htraversal [] rfl
  rw [hhandoff] at hvalid
  unfold validateHandoff at hvalid
  simp only [bind, Except.bind] at hvalid
  by_cases hmagic : input.magic != multiboot2Magic
  · rw [if_pos hmagic] at hvalid
    contradiction
  · rw [if_neg hmagic] at hvalid
    by_cases haddress :
        input.infoAddress ≥ wordLimit || low32Nat infoWord ≥ wordLimit ||
          low32Nat infoWord > wordLimit - 1 - input.infoAddress
    · rw [if_pos haddress] at hvalid
      contradiction
    · rw [if_neg haddress] at hvalid
      by_cases halignment : input.infoAddress % 8 != 0
      · rw [if_pos halignment] at hvalid
        contradiction
      · rw [if_neg halignment] at hvalid
        by_cases hsize :
            low32Nat infoWord < 16 || low32Nat infoWord % 8 != 0
        · rw [if_pos hsize] at hvalid
          contradiction
        · rw [if_neg hsize] at hvalid
          by_cases htagCount : tags.length > maxTags
          · rw [if_pos htagCount] at hvalid
            contradiction
          · rw [if_neg htagCount] at hvalid
            by_cases hshape :
                tags.any (fun tag => !tagShapeValid tag)
            · rw [if_pos hshape] at hvalid
              contradiction
            · rw [if_neg hshape] at hvalid
              let byteCount :=
                8 + (tags.map (aligned8 ∘ Tag.size)).foldl (· + ·) 0
              by_cases hbyteCount : byteCount != low32Nat infoWord
              · rw [if_pos hbyteCount] at hvalid
                contradiction
              · rw [if_neg hbyteCount] at hvalid
                by_cases hbound : byteCount > maxTagBytes
                · rw [if_pos hbound] at hvalid
                  contradiction
                · rw [if_neg hbound] at hvalid
                  have hsame : sourceEntries = decoded.entries := by
                    rw [hextract] at hvalid
                    injection hvalid
                  subst sourceEntries
                  exact ⟨entryOffset, entryCount, hsource⟩

structure ValidInfoAddress (address : Nat) : Type where
  atLeastPage : pageBytes ≤ address

def validateInfoAddress (address : Nat) : Except Error (ValidInfoAddress address) := do
  if address % 8 != 0 then throw .unalignedInfo
  if hbelow : address < pageBytes then
    throw .infoAddressBelowMinimum
  else
    pure ⟨Nat.le_of_not_gt hbelow⟩

def decode (input : Input) : Except Error Decoded := do
  if input.magic != multiboot2Magic then throw .badMagic
  let infoAddressValid ← validateInfoAddress input.infoAddress
  if input.bytes.length < 16 then throw .bufferTooSmall
  if input.bytes.length > maxTagBytes then throw .bufferTooLarge
  let infoWord ← readU64 input.bytes 0
  let totalSize := low32Nat infoWord
  let reserved := high32Nat infoWord
  if totalSize != input.bytes.length then throw .advertisedSizeMismatch
  if totalSize % 8 != 0 then throw .advertisedSizeMismatch
  if reserved != 0 then throw .nonzeroInfoReserved
  let tags ← decodeTags input.bytes totalSize 8 maxTags false []
  let handoff : Handoff :=
    { magic := input.magic, infoAddress := input.infoAddress, totalSize, tags }
  match hvalid : validateHandoff handoff with
  | .error reason => throw (.typedHandoffRejected reason)
  | .ok entries =>
      match hentries : validateEntries entries with
      | .error .zeroLength => throw .zeroLengthEntry
      | .error .addressOverflow => throw .entryAddressOverflow
      | .error reason => throw (.typedHandoffRejected reason)
      | .ok _ =>
          if hbounds : withinBounds handoff entries then
            pure ⟨handoff, entries, hvalid, hentries, hbounds,
              infoAddressValid.atLeastPage⟩
          else throw .internalBounds

namespace AcpiRootDecoder

open LeanOS.BootTopology

/-- Reuse the admitted immutable Multiboot2 copy, then perform one bounded
tag walk that projects only signature-, revision-, length-, and checksum-
validated ACPI tag 14/15 roots. -/
def decode (input : BootMemoryMapDecoder.Input) :
    Except Error (List RawAcpiRootTag) := do
  match BootMemoryMapDecoder.decode input with
  | .error reason => throw (.handoffRejected reason)
  | .ok _ =>
      let total ← match readU32 input.bytes 0 with
        | .ok value => pure value
        | .error _ => throw .truncatedTag
      scan input.bytes total 8 maxTags []

end AcpiRootDecoder

theorem decode_functional (input : Input) (first second : Except Error Decoded)
    (hfirst : decode input = first) (hsecond : decode input = second) : first = second := by
  rw [hfirst] at hsecond
  exact hsecond

/-- Every successful arbitrary rich decode constructs the recursive traversal
certificate.  No canonical fixture, scalar terminal word, or caller-provided
projection is used to obtain this evidence. -/
theorem successful_decode_constructs_traversal (input : Input) (decoded : Decoded)
    (h : decode input = .ok decoded) :
    SuccessfulRichDecodeTraversal input decoded := by
  unfold decode at h
  simp only [bind, Except.bind] at h
  by_cases hmagic : input.magic != multiboot2Magic
  · rw [if_pos hmagic] at h
    contradiction
  · rw [if_neg hmagic] at h
    cases haddress : validateInfoAddress input.infoAddress with
    | error reason =>
        simp only [haddress] at h
        contradiction
    | ok infoAddressValid =>
        simp only [haddress] at h
        by_cases hsmall : input.bytes.length < 16
        · rw [if_pos hsmall] at h
          contradiction
        · rw [if_neg hsmall] at h
          by_cases hlarge : input.bytes.length > maxTagBytes
          · rw [if_pos hlarge] at h
            contradiction
          · rw [if_neg hlarge] at h
            cases hword : readU64 input.bytes 0 with
            | error reason =>
                simp only [hword] at h
                contradiction
            | ok infoWord =>
                simp only [hword] at h
                by_cases hlength : low32Nat infoWord != input.bytes.length
                · rw [if_pos hlength] at h
                  contradiction
                · rw [if_neg hlength] at h
                  by_cases haligned : low32Nat infoWord % 8 != 0
                  · rw [if_pos haligned] at h
                    contradiction
                  · rw [if_neg haligned] at h
                    by_cases hzero : high32Nat infoWord != 0
                    · rw [if_pos hzero] at h
                      contradiction
                    · rw [if_neg hzero] at h
                      cases htags :
                          decodeTags input.bytes (low32Nat infoWord) 8 maxTags false [] with
                      | error reason =>
                          simp only [htags] at h
                          contradiction
                      | ok tags =>
                          simp only [htags] at h
                          split at h <;> try contradiction
                          next entries hvalid =>
                            split at h <;> try contradiction
                            next _ hentries =>
                              split at h <;> try contradiction
                              next hbounds =>
                                injection h with hdecoded
                                subst decoded
                                exact ⟨⟨infoWord, tags, hword,
                                  by simpa using hlength,
                                  by simpa using hzero,
                                  htags,
                                  decodeTags_constructs_traversal input.bytes
                                    (low32Nat infoWord) 8 maxTags false [] tags htags,
                                  rfl, hvalid, hentries, hbounds⟩⟩

/-- Successful decoding retains the exact scalar header fields supplied by the
immutable input.  This is the structural bridge used before proving the
streaming parser's terminal state. -/
theorem accepted_input_header (input : Input) (decoded : Decoded)
    (h : decode input = .ok decoded) :
    decoded.handoff.magic = input.magic ∧
      decoded.handoff.infoAddress = input.infoAddress ∧
      decoded.handoff.totalSize = input.bytes.length := by
  unfold decode at h
  simp only [bind, Except.bind] at h
  by_cases hmagic : input.magic != multiboot2Magic
  · rw [if_pos hmagic] at h
    contradiction
  · rw [if_neg hmagic] at h
    cases haddress : validateInfoAddress input.infoAddress with
    | error reason =>
        simp only [haddress] at h
        contradiction
    | ok infoAddressValid =>
        simp only [haddress] at h
        by_cases hsmall : input.bytes.length < 16
        · rw [if_pos hsmall] at h
          contradiction
        · rw [if_neg hsmall] at h
          by_cases hlarge : input.bytes.length > maxTagBytes
          · rw [if_pos hlarge] at h
            contradiction
          · rw [if_neg hlarge] at h
            cases hword : readU64 input.bytes 0 with
            | error reason =>
                simp only [hword] at h
                contradiction
            | ok infoWord =>
                simp only [hword] at h
                by_cases hlength : low32Nat infoWord != input.bytes.length
                · rw [if_pos hlength] at h
                  contradiction
                · rw [if_neg hlength] at h
                  by_cases haligned : low32Nat infoWord % 8 != 0
                  · rw [if_pos haligned] at h
                    contradiction
                  · rw [if_neg haligned] at h
                    by_cases hzero : high32Nat infoWord != 0
                    · rw [if_pos hzero] at h
                      contradiction
                    · rw [if_neg hzero] at h
                      cases htags :
                          decodeTags input.bytes (low32Nat infoWord) 8 maxTags false [] with
                      | error reason =>
                          simp only [htags] at h
                          contradiction
                      | ok tags =>
                          simp only [htags] at h
                          split at h <;> try contradiction
                          next entries hvalid =>
                            split at h <;> try contradiction
                            next _ hentries =>
                              split at h <;> try contradiction
                              next hbounds =>
                                injection h with hdecoded
                                subst decoded
                                exact ⟨rfl, rfl, by
                                  simpa using hlength⟩

/-- The immutable source header of every successful rich decode satisfies all
Nat-side admission conditions needed by the scalar streaming initializer.
This lemma deliberately stops at initialization; terminal parser and coverage
agreement remain the subsequent structural refinement. -/
theorem accepted_input_scalar_header (input : Input) (decoded : Decoded)
    (h : decode input = .ok decoded) :
    input.magic = multiboot2Magic ∧
      input.infoAddress < wordLimit ∧
      input.bytes.length < wordLimit ∧
      input.bytes.length ≤ wordLimit - 1 - input.infoAddress ∧
      input.infoAddress % 8 = 0 ∧
      16 ≤ input.bytes.length ∧
      input.bytes.length % 8 = 0 ∧
      input.bytes.length ≤ maxTagBytes ∧
      pageBytes ≤ input.infoAddress := by
  have hheader := accepted_input_header input decoded h
  have hvalid := decoded.handoffValid
  unfold validateHandoff at hvalid
  simp only [bind, Except.bind] at hvalid
  by_cases hmagic : decoded.handoff.magic != multiboot2Magic
  · rw [if_pos hmagic] at hvalid
    contradiction
  · rw [if_neg hmagic] at hvalid
    by_cases hoverflow :
        decoded.handoff.infoAddress ≥ wordLimit ||
          decoded.handoff.totalSize ≥ wordLimit ||
          decoded.handoff.totalSize >
            wordLimit - 1 - decoded.handoff.infoAddress
    · rw [if_pos hoverflow] at hvalid
      contradiction
    · rw [if_neg hoverflow] at hvalid
      by_cases haligned : decoded.handoff.infoAddress % 8 != 0
      · rw [if_pos haligned] at hvalid
        contradiction
      · rw [if_neg haligned] at hvalid
        by_cases hsize :
            decoded.handoff.totalSize < 16 ||
              decoded.handoff.totalSize % 8 != 0
        · rw [if_pos hsize] at hvalid
          contradiction
        · have hbounds := decoded.bounds
          simp only [withinBounds, Bool.and_eq_true, decide_eq_true_eq] at hbounds
          simp at hoverflow hsize hmagic haligned
          rw [← hheader.1, ← hheader.2.1, ← hheader.2.2]
          exact ⟨hmagic, by omega, by omega, by omega, haligned,
            by omega, by omega, hbounds.1.1, decoded.infoAddressAtLeastPage⟩

/-- Every accepted rich result carries the same low-address admission fact as
the scalar production initializer.  This removes the aligned-address gap where
the rich decoder could previously accept an identity below 4 KiB that the
scalar replay necessarily rejected before reading any bytes. -/
theorem accepted_infoAddress_at_least_page (decoded : Decoded) :
    pageBytes ≤ decoded.handoff.infoAddress :=
  decoded.infoAddressAtLeastPage

theorem accepted_handoff_valid (input : Input) (decoded : Decoded)
    (_h : decode input = .ok decoded) :
    validateHandoff decoded.handoff = .ok decoded.entries :=
  decoded.handoffValid

set_option maxHeartbeats 800000 in
/-- Successful handoff validation reaches the exact typed map extraction;
none of the preceding shape checks can replace its returned entry list. -/
theorem validateHandoff_extractMemoryMap
    (handoff : Handoff) (entries : List RawEntry)
    (hvalid : validateHandoff handoff = .ok entries) :
    extractMemoryMap handoff.tags = .ok entries := by
  unfold validateHandoff at hvalid
  simp only [bind, Except.bind] at hvalid
  by_cases hmagic : handoff.magic != multiboot2Magic
  · rw [if_pos hmagic] at hvalid
    contradiction
  · rw [if_neg hmagic] at hvalid
    by_cases hoverflow :
        handoff.infoAddress ≥ wordLimit || handoff.totalSize ≥ wordLimit ||
          handoff.totalSize > wordLimit - 1 - handoff.infoAddress
    · rw [if_pos hoverflow] at hvalid
      contradiction
    · rw [if_neg hoverflow] at hvalid
      by_cases haligned : handoff.infoAddress % 8 != 0
      · rw [if_pos haligned] at hvalid
        contradiction
      · rw [if_neg haligned] at hvalid
        by_cases hsize :
            handoff.totalSize < 16 || handoff.totalSize % 8 != 0
        · rw [if_pos hsize] at hvalid
          contradiction
        · rw [if_neg hsize] at hvalid
          by_cases htags : handoff.tags.length > maxTags
          · rw [if_pos htags] at hvalid
            contradiction
          · rw [if_neg htags] at hvalid
            by_cases hshape : handoff.tags.any (fun tag => !tagShapeValid tag)
            · rw [if_pos hshape] at hvalid
              contradiction
            · rw [if_neg hshape] at hvalid
              let bytes :=
                8 + (handoff.tags.map (aligned8 ∘ Tag.size)).foldl (· + ·) 0
              change
                (if bytes != handoff.totalSize then
                  throw .malformedInfoSize
                else if bytes > maxTagBytes then
                  throw .tagBytesExceeded
                else extractMemoryMap handoff.tags) = .ok entries at hvalid
              by_cases hbytes : bytes != handoff.totalSize
              · rw [if_pos hbytes] at hvalid
                contradiction
              · rw [if_neg hbytes] at hvalid
                by_cases hbound : bytes > maxTagBytes
                · rw [if_pos hbound] at hvalid
                  contradiction
                · rw [if_neg hbound] at hvalid
                  exact hvalid

theorem accepted_within_bounds (input : Input) (decoded : Decoded)
    (_h : decode input = .ok decoded) :
    withinBounds decoded.handoff decoded.entries = true :=
  decoded.bounds

theorem accepted_entries_valid (input : Input) (decoded : Decoded)
    (_h : decode input = .ok decoded) :
    validateEntries decoded.entries = .ok () :=
  decoded.entriesValid

def decodeHandoff (input : Input) : Except Error Handoff :=
  (decode input).map (·.handoff)

theorem rejected_has_no_handoff (input : Input) (reason : Error)
    (h : decodeHandoff input = .error reason) :
    (decodeHandoff input).toOption = none := by
  rw [h]
  rfl

inductive PipelineError where
  | decode (reason : Error)
  | normalize (reason : BootMemoryMap.Error)
  deriving BEq, DecidableEq, Repr

def decodeAndNormalize (input : Input) : Except PipelineError Normalized := do
  match decode input with
  | .error reason => .error (.decode reason)
  | .ok decoded =>
      match normalize decoded.handoff with
      | .error reason => .error (.normalize reason)
      | .ok result => .ok result

theorem accepted_pipeline_has_handoff (input : Input) (result : Normalized)
    (h : decodeAndNormalize input = .ok result) :
    ∃ decoded, decode input = .ok decoded ∧ normalize decoded.handoff = .ok result := by
  unfold decodeAndNormalize at h
  cases hdecode : decode input with
  | error reason =>
      rw [hdecode] at h
      contradiction
  | ok decoded =>
      rw [hdecode] at h
      dsimp only at h
      cases hnormalize : normalize decoded.handoff with
      | error reason =>
          rw [hnormalize] at h
          contradiction
      | ok normalized =>
          rw [hnormalize] at h
          injection h with heq
          subst result
          exact ⟨decoded, rfl, hnormalize⟩

theorem rejected_pipeline_has_no_normalized (input : Input) (reason : PipelineError)
    (h : decodeAndNormalize input = .error reason) :
    (decodeAndNormalize input).toOption = none := by
  rw [h]
  rfl

namespace Fixtures

open LeanOS.BootTopology

def byte (value : Nat) : UInt8 := UInt8.ofNat value

def encodeLE (width value : Nat) : List UInt8 :=
  (List.range width).map fun index => byte ((value / (256 ^ index)) % 256)

def u32 (value : Nat) : List UInt8 := encodeLE 4 value
def u64 (value : Nat) : List UInt8 := encodeLE 8 value
def zeroes (count : Nat) : List UInt8 := List.replicate count 0

def entry (base length kind : Nat) (reserved := 0) : List UInt8 :=
  u64 base ++ u64 length ++ u32 kind ++ u32 reserved

def tag (tagType : Nat) (payload : List UInt8) (paddingByte := byte 0) : List UInt8 :=
  let size := 8 + payload.length
  u32 tagType ++ u32 size ++ payload ++ List.replicate (aligned8 size - size) paddingByte

def memoryMapTag (entries : List (List UInt8)) (entrySize := memoryMapEntrySize)
    (entryVersion := 0) : List UInt8 :=
  tag 6 (u32 entrySize ++ u32 entryVersion ++ entries.flatten)

def endTag : List UInt8 := u32 0 ++ u32 8

def information (tags : List UInt8) (reserved := 0) : List UInt8 :=
  let total := 8 + tags.length
  u32 total ++ u32 reserved ++ tags

def sampleEntries : List (List UInt8) :=
  [entry 0x1000 0x4000 1, entry 0x2000 0x1000 2]

def sampleBytes : List UInt8 :=
  information (tag 42 [byte 0xaa] ++ memoryMapTag sampleEntries ++ endTag)

def sampleInput : Input :=
  { magic := multiboot2Magic, infoAddress := 0x1000, bytes := sampleBytes }

private def checksumByte (bytes : List UInt8) : UInt8 :=
  byte ((256 - bytes.foldl (fun total value => (total + value.toNat) % 256) 0) % 256)

private def replaceByte (bytes : List UInt8) (index : Nat) (value : UInt8) :
    List UInt8 :=
  bytes.take index ++ [value] ++ bytes.drop (index + 1)

def oldRsdp (revision := 0) : List UInt8 :=
  let unchecked :=
    [byte 0x52, byte 0x53, byte 0x44, byte 0x20, byte 0x50, byte 0x54,
      byte 0x52, byte 0x20, byte 0, byte 0x51, byte 0x45, byte 0x4d,
      byte 0x55, byte 0x20, byte 0x20, byte revision] ++ u32 0x000f5b70
  replaceByte unchecked 8 (checksumByte unchecked)

def newRsdp (declaredLength := 36) : List UInt8 :=
  let unchecked := oldRsdp 2 ++ u32 declaredLength ++
    u64 0x00000000000f5c00 ++ [byte 0, byte 0, byte 0, byte 0]
  replaceByte unchecked 32 (checksumByte unchecked)

def conflictingNewRsdp : List UInt8 :=
  let changedOem := replaceByte newRsdp 9 (byte 0x42)
  let legacyCleared := replaceByte changedOem 8 0
  let legacyRepaired := replaceByte legacyCleared 8
    (checksumByte (legacyCleared.take 20))
  let extendedCleared := replaceByte legacyRepaired 32 0
  replaceByte extendedCleared 32 (checksumByte extendedCleared)

def acpiInput (rootTags : List UInt8) : Input :=
  { sampleInput with
    bytes := information (rootTags ++ memoryMapTag sampleEntries ++ endTag) }

def acpiErrorOf {α : Type} :
    Except AcpiRootDecoder.Error α → Option AcpiRootDecoder.Error
  | .error reason => some reason
  | .ok _ => none

example : (AcpiRootDecoder.decode (acpiInput (tag 14 oldRsdp))).toOption.map
    (·.length) = some 1 := by native_decide

example : (AcpiRootDecoder.decode (acpiInput (tag 15 newRsdp))).toOption.map
    (·.length) = some 1 := by native_decide

example : (AcpiRootDecoder.decode
    (acpiInput (tag 14 oldRsdp ++ tag 15 newRsdp))).toOption.map
      (fun roots => match selectAcpiRoot roots with
        | .ok root => root == {
            source := .newRsdp
            legacy := repositoryLegacyRoot
            xsdtAddress := some 0x00000000000f5c00
          }
        | .error _ => false) = some true := by native_decide

example : (AcpiRootDecoder.decode
    (acpiInput (tag 14 oldRsdp ++ tag 15 conflictingNewRsdp))).toOption.map
      (fun roots => match selectAcpiRoot roots with
        | .error reason => reason == .conflictingRoots
        | .ok _ => false) =
    some true := by native_decide

example : acpiErrorOf (AcpiRootDecoder.decode
    (acpiInput (tag 14 (replaceByte oldRsdp 0 (byte 0))))) =
    some .invalidSignature := by native_decide

example : acpiErrorOf (AcpiRootDecoder.decode
    (acpiInput (tag 14 (replaceByte oldRsdp 9 (byte 0))))) =
    some .invalidLegacyChecksum := by native_decide

example : acpiErrorOf (AcpiRootDecoder.decode
    (acpiInput (tag 15 (newRsdp 40)))) =
    some .invalidRsdpLength := by native_decide

def sampleHandoff : Handoff :=
  { magic := multiboot2Magic, infoAddress := 0x1000, totalSize := sampleBytes.length,
    tags :=
      [.ignored 9,
       .memoryMap (memoryMapTagHeaderSize + memoryMapEntrySize * 2)
         memoryMapEntrySize 0
         [{ base := 0x1000, length := 0x4000, kind := .usable },
          { base := 0x2000, length := 0x1000, kind := .reserved }],
       .end 8] }

example : (decode sampleInput).toOption.map (·.handoff) = some sampleHandoff := by
  native_decide

example : (decodeAndNormalize sampleInput).toOption.map (·.regions) = some
    [{ start := 1, count := 1, kind := .usable },
     { start := 2, count := 1, kind := .reserved },
     { start := 3, count := 2, kind := .usable }] := by
  native_decide

def withBytes (bytes : List UInt8) : Input := { sampleInput with bytes }

def errorOf {α : Type} : Except Error α → Option Error
  | .error reason => some reason
  | .ok _ => none

def pipelineErrorOf {α : Type} : Except PipelineError α → Option PipelineError
  | .error reason => some reason
  | .ok _ => none

example : errorOf (decode { sampleInput with infoAddress := pageBytes - 8 }) =
    some .infoAddressBelowMinimum := by native_decide

/-- A buffer ending exactly at `2^64` cannot be represented by the scalar
initializer and is rejected by the rich decoder as well. -/
example :
    errorOf
        (decode
          { sampleInput with
            infoAddress := wordLimit - sampleBytes.length }) =
      some (.typedHandoffRejected .addressOverflow) := by native_decide

example : errorOf (decode (withBytes (sampleBytes.take (sampleBytes.length - 1)))) =
    some .advertisedSizeMismatch := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries ++ memoryMapTag sampleEntries ++ endTag)))) =
    some .duplicateMemoryMap := by native_decide

example : errorOf (decode (withBytes (information (memoryMapTag sampleEntries)))) =
    some .missingEndTag := by native_decide

example : errorOf (decode (withBytes
    (information (endTag ++ memoryMapTag sampleEntries ++ endTag)))) =
    some .misplacedEndTag := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries (entrySize := 32) ++ endTag)))) =
    some .badEntrySize := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag sampleEntries (entryVersion := 1) ++ endTag)))) =
    some .unsupportedEntryVersion := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag [entry 0 0x1000 1 1] ++ endTag)))) =
    some .nonzeroEntryReserved := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag [entry 0 0 1] ++ endTag)))) =
    some .zeroLengthEntry := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag [entry (wordLimit - 1) 2 1] ++ endTag)))) =
    some .entryAddressOverflow := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag [entry 1 (wordLimit - 1) 1] ++ endTag)))) =
    some .entryAddressOverflow := by native_decide

example : ((decode (withBytes
    (information (tag 42 [byte 0xaa] (paddingByte := byte 1) ++
      memoryMapTag sampleEntries ++ endTag)))).toOption.map (·.handoff)) =
    some sampleHandoff := by native_decide

example : ((decode (withBytes
    (information (memoryMapTag [entry 0 0x1000 99] ++ endTag)))).toOption.map
      (·.entries)) =
    some [{ base := 0, length := 0x1000, kind := .reserved }] := by native_decide

example : errorOf
    (decode (withBytes (information (memoryMapTag sampleEntries ++ endTag) 1))) =
    some .nonzeroInfoReserved := by native_decide

def ignoredTags (count : Nat) : List UInt8 :=
  (List.replicate count (tag 42 [])).flatten

def repeatedEntries (count : Nat) : List (List UInt8) :=
  (List.range count).map fun frame => entry (frame * pageBytes) pageBytes 1

def repeatedEntryInput (count : Nat) : Input :=
  withBytes (information (memoryMapTag (repeatedEntries count) ++ endTag))

example : errorOf (decode (withBytes (zeroes (maxTagBytes + 1)))) =
    some .bufferTooLarge := by native_decide

example : errorOf
    (decode (withBytes (information (ignoredTags maxTags ++ endTag)))) =
    some .tooManyTags := by native_decide

example : errorOf (decode (withBytes
    (information (memoryMapTag (repeatedEntries (maxEntries + 1)) ++ endTag)))) =
    some .tooManyEntries := by native_decide

example : (decode (repeatedEntryInput 128)).toOption.map (·.entries.length) =
    some 128 := by native_decide

example : (decode (repeatedEntryInput 129)).toOption.map (·.entries.length) =
    some 129 := by native_decide

example : (decode (repeatedEntryInput 256)).toOption.map (·.entries.length) =
    some maxEntries := by native_decide

example : errorOf (decode (repeatedEntryInput 257)) =
    some .tooManyEntries := by native_decide

example : errorOf (decode (withBytes
    (information (u32 42 ++ u32 24 ++ endTag)))) =
    some .tagOutOfBounds := by native_decide

example : pipelineErrorOf (decodeAndNormalize (withBytes
    (information (memoryMapTag [entry (wordLimit - 1) 2 1] ++ endTag)))) =
    some (.decode .entryAddressOverflow) := by native_decide

example : pipelineErrorOf (decodeAndNormalize (withBytes
    (information (memoryMapTag [entry 0 0 1] ++ endTag)))) =
    some (.decode .zeroLengthEntry) := by native_decide

end Fixtures

end LeanOS.BootMemoryMapDecoder
