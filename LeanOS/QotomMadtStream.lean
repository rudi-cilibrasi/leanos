import LeanOS.QotomBspTopology
import Std.Tactic.BVDecide

/-! Allocation-free byte stream for the Qotom processor inventory candidate.

This consumes an independently envelope-validated MADT, starting at byte 44.
The caller must carry exactly the returned scalar state into the next call.
Status 3 establishes only completed processor inventory, not runtime admission.
Root/copy validation, BSP register binding, interrupt routing and AP dormancy
remain separate obligations. The byte stream consumes type-4 routing bytes
without interpreting them; the composed consumer applies the quarantine gate
defined below.

The scalar layout mirrors the existing q35 stream; the q35 function is unchanged.
Errors 69--74 retain its framing/record/online-capable/duplicate meanings;
75 rejects a count other than four, 76 rejects executing ID other than zero,
and 77 rejects disabled, extra, or out-of-order processor records.
-/
namespace LeanOS.QotomMadtStream

open BootTopology

/-! ### Malformed native Local APIC NMI quarantine

The physical MADT contains four type-4 records whose reserved flag bits and
LINT values are invalid.  They are retained byte for byte, but they must never
be interpreted as interrupt-routing authority.  This small scalar gate binds
the exact observation to the production candidate's disabled-routing policy.
-/

/-- Six-byte MADT records packed little-endian, in physical table order. -/
def nativeLocalApicNmi0 : UInt64 := 0x0000f751dc010604
def nativeLocalApicNmi1 : UInt64 := 0x0000a67499020604
def nativeLocalApicNmi2 : UInt64 := 0x0000ce213a030604
def nativeLocalApicNmi3 : UInt64 := 0x0000279e9d040604

def nativeLocalApicNmiRecords : List UInt64 :=
  [nativeLocalApicNmi0, nativeLocalApicNmi1,
   nativeLocalApicNmi2, nativeLocalApicNmi3]

@[inline] def localApicNmiFlags (record : UInt64) : UInt64 :=
  (record >>> 24) &&& 0xffff

@[inline] def localApicNmiLint (record : UInt64) : UInt64 :=
  (record >>> 40) &&& 0xff

/-- ACPI MPS INTI flags have twelve zero reserved bits and no reserved
polarity/trigger encoding; a Local APIC NMI may name only LINT0 or LINT1. -/
def localApicNmiUsable (record : UInt64) : Bool :=
  let flags := localApicNmiFlags record
  flags &&& 0xfff0 == 0 && flags &&& 3 != 2 && (flags >>> 2) &&& 3 != 2 &&
    localApicNmiLint record <= 1

theorem native_local_apic_nmi_records_are_unusable :
    nativeLocalApicNmiRecords.all (fun record => !localApicNmiUsable record) = true := by
  native_decide

/-- Result words are ABI/status/error/policy/count.  Policy 1 means the exact
malformed records were recognized and quarantined while routing authority
remained disabled.  Errors 87--89 cover count, byte drift, and attempted use. -/
def nmiPolicyQuery
    (count first second third fourth routingAuthority word : UInt64) : UInt64 :=
  let error :=
    if count != 4 then 87
    else if first != nativeLocalApicNmi0 || second != nativeLocalApicNmi1 ||
        third != nativeLocalApicNmi2 || fourth != nativeLocalApicNmi3 then 88
    else if routingAuthority != 0 then 89
    else 0
  if word == 0 then 1
  else if word == 1 then if error == 0 then 1 else 2
  else if word == 2 then error
  else if word == 3 && error == 0 then 1
  else if word == 4 && error == 0 then count
  else 0

theorem nmi_policy_acceptance_iff
    (count first second third fourth routingAuthority : UInt64) :
    nmiPolicyQuery count first second third fourth routingAuthority 1 = 1 ↔
      count = 4 ∧ first = nativeLocalApicNmi0 ∧
      second = nativeLocalApicNmi1 ∧ third = nativeLocalApicNmi2 ∧
      fourth = nativeLocalApicNmi3 ∧ routingAuthority = 0 := by
  unfold nmiPolicyQuery
  by_cases hc : count = 4 <;>
  by_cases h0 : first = nativeLocalApicNmi0 <;>
  by_cases h1 : second = nativeLocalApicNmi1 <;>
  by_cases h2 : third = nativeLocalApicNmi2 <;>
  by_cases h3 : fourth = nativeLocalApicNmi3 <;>
  by_cases hr : routingAuthority = 0 <;> simp_all
  repeat' (split <;> simp_all)

theorem nmi_policy_never_authorizes_routing
    (count first second third fourth routingAuthority : UInt64)
    (accepted : nmiPolicyQuery count first second third fourth routingAuthority 1 = 1) :
    routingAuthority = 0 :=
  (nmi_policy_acceptance_iff count first second third fourth routingAuthority).mp accepted |>.2.2.2.2.2

@[export leanos_qotom_madt_nmi_policy_query]
def exportedNmiPolicyQuery
    (count first second third fourth routingAuthority word : UInt64) : UInt64 :=
  nmiPolicyQuery count first second third fourth routingAuthority word

/-- One completed processor must be the next enabled baseline member. -/
@[inline] def processorMatches (position apicId : UInt64) (enabled : Bool) : Bool :=
  position < 4 && apicId == position * 2 && enabled

theorem processor_matches_iff (position apicId : UInt64) (enabled : Bool) :
    processorMatches position apicId enabled = true ↔
      position < 4 ∧ apicId = position * 2 ∧ enabled = true := by
  simp [processorMatches, and_assoc]

theorem processor_matches_rejects_disabled (position apicId : UInt64) :
    processorMatches position apicId false = false := by
  simp [processorMatches]

/-- The scalar processor guard selects exactly the corresponding typed
baseline record when the independently checked online-capable bit is clear. -/
theorem processor_matches_typed_record (position : UInt64) (processor : Processor)
    (matched : processorMatches position processor.apicId.toUInt64 processor.enabled = true)
    (offline : processor.onlineCapable = false) :
    some processor = QotomBspTopology.processors[position.toNat]? := by
  have conditions := (processor_matches_iff _ _ _).mp matched
  have positions : position = 0 ∨ position = 1 ∨ position = 2 ∨ position = 3 := by
    have bound := conditions.1
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at *
    simp at *
    omega
  rcases processor with ⟨id, enabled, online⟩
  rcases positions with h | h | h | h <;> subst position <;>
    simp_all [QotomBspTopology.processors]
  all_goals
    simp only [← UInt64.toNat_inj] at conditions
    simp at conditions
    simp only [← UInt32.toNat_inj]
    simp_all

/-- Four decoded records satisfying the actual scalar guard at each index
form exactly the typed baseline inventory. Parsing must establish these guards. -/
theorem guarded_processors_equal_baseline (observed : List Processor)
    (count : observed.length = 4)
    (guards : ∀ (index : Nat) (within : index < observed.length),
      processorMatches (UInt64.ofNat index) observed[index].apicId.toUInt64
        observed[index].enabled = true ∧ observed[index].onlineCapable = false) :
    observed = QotomBspTopology.processors := by
  apply List.ext_getElem
  · simpa [QotomBspTopology.processors] using count
  · intro index left right
    have checked := guards index left
    have same := processor_matches_typed_record (UInt64.ofNat index)
      observed[index] checked.1 checked.2
    have bounded : index < 4 := by omega
    have index_exact : (UInt64.ofNat index).toNat = index := by
      simp
      omega
    simpa [index_exact, List.getElem?_eq_getElem right] using same

def byteStepQuery
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64) : UInt64 :=
  if word > 15 then 0 else
  let malformedState := currentOffset != byteOffset || byteOffset < 44 ||
    byteOffset >= tableLength || tableLength < 44 ||
    tableLength > UInt64.ofNat maxAcpiSdtBytes || recordOffset > 11 ||
    recordKind > 0xff || recordLength > 12 || apicId > 0xff ||
    flags > 0xffffffff || enabledCount > 4 || admittedApicId > 256 ||
    executingApicId > 0xff || byteValue > 0xff
  let nextKind := if recordOffset == 0 then byteValue else recordKind
  let kindError := recordOffset == 0 && nextKind != 0 && nextKind != 1 &&
    nextKind != 2 && nextKind != 4
  let expectedLength :=
    if nextKind == 0 then 8
    else if nextKind == 1 then 12
    else if nextKind == 2 then 10
    else if nextKind == 4 then 6
    else 0
  let nextLength := if recordOffset == 1 then byteValue else recordLength
  let lengthError := recordOffset == 1 && nextLength != expectedLength
  let nextApicId :=
    if nextKind == 0 && recordOffset == 3 then byteValue else apicId
  let flagsShift := (recordOffset - 4) * 8
  let nextFlags :=
    if nextKind == 0 && recordOffset >= 4 then
      flags ||| (byteValue <<< flagsShift)
    else flags
  let recordComplete := nextLength != 0 && recordOffset + 1 == nextLength
  let tableComplete := byteOffset + 1 == tableLength
  let truncationError := tableComplete && !recordComplete
  let onlineCapableError := recordComplete && nextKind == 0 &&
    (nextFlags &&& 2) != 0
  let seenIndex := nextApicId / 64
  let seenBit := (1 : UInt64) <<< (nextApicId % 64)
  let duplicate := recordComplete && nextKind == 0 &&
    ((seenIndex == 0 && (seen0 &&& seenBit) != 0) ||
     (seenIndex == 1 && (seen1 &&& seenBit) != 0) ||
     (seenIndex == 2 && (seen2 &&& seenBit) != 0) ||
     (seenIndex == 3 && (seen3 &&& seenBit) != 0))
  let enabled := recordComplete && nextKind == 0 && (nextFlags &&& 1) != 0
  let nextEnabledCount := if enabled then enabledCount + 1 else enabledCount
  let nextAdmittedApicId :=
    if enabled && enabledCount == 0 then nextApicId else admittedApicId
  let nextSeen0 :=
    if recordComplete && nextKind == 0 && seenIndex == 0 then seen0 ||| seenBit
    else seen0
  let nextSeen1 :=
    if recordComplete && nextKind == 0 && seenIndex == 1 then seen1 ||| seenBit
    else seen1
  let nextSeen2 :=
    if recordComplete && nextKind == 0 && seenIndex == 2 then seen2 ||| seenBit
    else seen2
  let nextSeen3 :=
    if recordComplete && nextKind == 0 && seenIndex == 3 then seen3 ||| seenBit
    else seen3
  -- Every processor record must occupy the next exact baseline position.
  -- Count all processor records by rejecting disabled records immediately.
  let inventoryError := recordComplete && nextKind == 0 &&
    !processorMatches enabledCount nextApicId enabled
  let inventoryCountError := tableComplete && recordComplete &&
    nextEnabledCount != 4
  let executingError := tableComplete && recordComplete &&
    (executingApicId != 0 || nextAdmittedApicId != 0)
  let error :=
    if malformedState then 69
    else if kindError then 70
    else if lengthError then 71
    else if truncationError then 72
    else if onlineCapableError then 73
    else if duplicate then 74
    else if inventoryError then 77
    else if inventoryCountError then 75
    else if executingError then 76
    else 0
  if word == 0 then 1
  else if word == 1 then
    if error != 0 then 2 else if tableComplete then 3 else 1
  else if word == 2 then error
  else if error != 0 then 0
  else if word == 3 then byteOffset + 1
  else if word == 4 then if recordComplete then 0 else recordOffset + 1
  else if word == 5 then if recordComplete then 0 else nextKind
  else if word == 6 then if recordComplete then 0 else nextLength
  else if word == 7 then if recordComplete then 0 else nextApicId
  else if word == 8 then if recordComplete then 0 else nextFlags
  else if word == 9 then nextEnabledCount
  else if word == 10 then nextAdmittedApicId
  else if word == 11 then nextSeen0
  else if word == 12 then nextSeen1
  else if word == 13 then nextSeen2
  else if word == 14 then nextSeen3
  else if word == 15 then byteValue
  else 0

/-- Bitwise byte accumulation and the authoritative decoder's natural-number
little-endian arithmetic produce exactly the same flags value, without wrap. -/
theorem flags_bytes_match_reference (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
      (b3.toUInt64 <<< 24)).toNat =
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 := by
  have words :
      b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) =
      b0.toUInt64 + b1.toUInt64 * 256 + b2.toUInt64 * 65536 +
        b3.toUInt64 * 16777216 := by
    bv_decide
  rw [words]
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp [UInt64.toNat_add, UInt64.toNat_mul]
  omega

/-- Both processor flag predicates agree with the reference decoder for all
four-byte payloads, including reserved high bits. -/
theorem flags_predicates_match_reference (b0 b1 b2 b3 : UInt8) :
    let word := b0.toUInt64 ||| (b1.toUInt64 <<< 8) |||
      (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)
    let value := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
    (word &&& 1 != 0) = (value % 2 == 1) ∧
      (word &&& 2 != 0) = ((value / 2) % 2 == 1) := by
  have enabled (word : UInt64) : (word &&& 1 != 0) = (word % 2 == 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, beq_iff_eq]
    bv_decide
  have online (word : UInt64) : (word &&& 2 != 0) = ((word / 2) % 2 == 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, beq_iff_eq]
    bv_decide
  dsimp only
  rw [enabled, online]
  constructor <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [beq_iff_eq, ← UInt64.toNat_inj] <;>
    simp only [UInt64.toNat_mod, UInt64.toNat_div, flags_bytes_match_reference] <;>
    simp

/-- The APIC-ID byte is retained exactly, rather than supplied from an
expected inventory value, on every successful local-APIC transition. -/
theorem processor_id_byte_retained
    (currentOffset apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 3 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    byteStepQuery currentOffset 3 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 7 = byteValue := by
  simp [byteStepQuery] at accepted ⊢
  repeat' (split at accepted <;> (try simp_all))

/-- Each nonterminal flags byte contributes at its little-endian position
while preserving the supplied accumulator. Whole-stream provenance additionally
requires that accumulator to come from the preceding successful transition. -/
theorem processor_flags_byte_accumulated
    (currentOffset recordOffset apicId flags enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue : UInt64)
    (position : recordOffset = 4 ∨ recordOffset = 5 ∨ recordOffset = 6)
    (accepted : byteStepQuery currentOffset recordOffset 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    byteStepQuery currentOffset recordOffset 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 8 = flags ||| (byteValue <<< ((recordOffset - 4) * 8)) := by
  rcases position with h | h | h <;> subst recordOffset <;>
    simp [byteStepQuery] at accepted ⊢
  all_goals repeat' (split at accepted <;> (try simp_all))

/-- Every successful nonterminal local-APIC payload byte updates only its
specified ID/flags field and record offset, preserving the complete inventory. -/
theorem processor_payload_fields
    (currentOffset recordOffset apicId flags enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue : UInt64)
    (lower : 2 ≤ recordOffset) (upper : recordOffset < 7)
    (accepted : byteStepQuery currentOffset recordOffset 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset recordOffset 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue
    (query 4, query 5, query 6, query 7, query 8) =
      (recordOffset + 1, 0, 8, if recordOffset = 3 then byteValue else apicId,
        if 4 ≤ recordOffset then flags ||| (byteValue <<< ((recordOffset - 4) * 8)) else flags) ∧
    (query 9, query 10, query 11, query 12, query 13, query 14) =
      (enabledCount, admittedApicId, seen0, seen1, seen2, seen3) := by
  have positions : recordOffset = 2 ∨ recordOffset = 3 ∨ recordOffset = 4 ∨
      recordOffset = 5 ∨ recordOffset = 6 := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at *
    simp at *
    omega
  rcases positions with h | h | h | h | h <;> subst recordOffset <;>
    simp [byteStepQuery] at accepted ⊢
  all_goals repeat' (split at accepted <;> (try simp_all))

/-- The final byte of an eight-byte local-APIC record can report no error
only when its reconstructed flags and APIC ID pass the inventory guard. -/
theorem completed_processor_requires_guard
    (currentOffset apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    processorMatches enabledCount apicId
      ((flags ||| (byteValue <<< 24)) &&& 1 != 0) = true ∧
    (flags ||| (byteValue <<< 24)) &&& 2 = 0 := by
  simp [byteStepQuery] at accepted
  repeat' (split at accepted <;> (try simp_all))

/-- A successful completed processor record advances the processor position
by exactly one; disabled records cannot preserve the count and slip through. -/
theorem completed_processor_advances_count
    (currentOffset apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 9 = enabledCount + 1 := by
  have guarded := completed_processor_requires_guard currentOffset apicId flags
    enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
    byteOffset byteValue accepted
  have enabled := (processor_matches_iff _ _ _).mp guarded.1
  simp [byteStepQuery] at accepted ⊢
  repeat' (split at accepted <;> (try simp_all))

/-- Completing a guarded processor adds exactly its next baseline ID bit
to the first duplicate-detection limb and preserves the other three limbs. -/
theorem completed_processor_seen_bits
    (currentOffset apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue
    (query 11, query 12, query 13, query 14) =
      (seen0 ||| ((1 : UInt64) <<< (enabledCount * 2)), seen1, seen2, seen3) := by
  have guarded := completed_processor_requires_guard currentOffset apicId flags
    enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
    byteOffset byteValue accepted
  have matched := (processor_matches_iff _ _ _).mp guarded.1
  have positions : enabledCount = 0 ∨ enabledCount = 1 ∨ enabledCount = 2 ∨ enabledCount = 3 := by
    have bound := matched.1
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at *
    simp at *
    omega
  have actualId := matched.2.1
  clear guarded matched
  rcases positions with h | h | h | h <;> subst enabledCount <;>
    simp at actualId <;> subst apicId <;>
    simp [byteStepQuery] at accepted ⊢
  all_goals repeat' (split at accepted <;> (try simp_all))

/-- A completed local-APIC record clears every partial-record field before
another record starts. A prior record's ID or flags cannot carry over. -/
theorem completed_processor_clears_partial_state
    (currentOffset apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue word : UInt64)
    (field : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 ∨ word = 8)
 :
    byteStepQuery currentOffset 7 0 8 apicId flags enabledCount
      admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId
      byteOffset byteValue word = 0 := by
  rcases field with h | h | h | h | h <;> subst word <;>
    simp [byteStepQuery]

/-- On success the exposed next byte offset advances exactly once. -/
theorem successful_byte_advances_offset
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 = 0) :
    byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 3 = byteOffset + 1 := by
  simp [byteStepQuery] at accepted ⊢
  intro rejected
  exact (rejected accepted).elim

/-- Successful byte transitions are bound to the caller's current offset
inside the bounded MADT, so the next-offset addition cannot wrap. -/
theorem successful_byte_position_bounded
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 = 0) :
    currentOffset = byteOffset ∧ 44 ≤ byteOffset ∧ byteOffset < tableLength ∧
      tableLength ≤ UInt64.ofNat maxAcpiSdtBytes := by
  have same : currentOffset = byteOffset := by
    apply Classical.byContradiction
    intro h
    simp [byteStepQuery, h] at accepted
  have low : 44 ≤ byteOffset := by
    apply Classical.byContradiction
    intro h
    have bad := UInt64.not_le.mp h
    simp [byteStepQuery, bad] at accepted
  have within : byteOffset < tableLength := by
    apply Classical.byContradiction
    intro h
    have bad := UInt64.not_lt.mp h
    simp [byteStepQuery, bad] at accepted
  have bound : tableLength ≤ UInt64.ofNat maxAcpiSdtBytes := by
    apply Classical.byContradiction
    intro h
    have bad := UInt64.not_le.mp h
    simp [byteStepQuery, bad] at accepted
  exact ⟨same, low, within, bound⟩

/-- Once a non-processor record's kind byte is retained, its remaining bytes
cannot change the processor count, admitted ID or any duplicate-detection limb. -/
theorem nonprocessor_preserves_inventory
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (pastKind : recordOffset ≠ 0) (nonprocessor : recordKind ≠ 0)
    (accepted : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue
    (query 9, query 10, query 11, query 12, query 13, query 14) =
      (enabledCount, admittedApicId, seen0, seen1, seen2, seen3) := by
  simp [byteStepQuery, pastKind, nonprocessor] at accepted ⊢
  repeat' (split at accepted <;> (try simp_all))

/-- Starting a record from cleared partial state retains its actual kind byte,
sets the next record offset to one, and preserves all processor inventory. -/
theorem record_kind_starts_clean
    (currentOffset enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 0 0 0 0 0 enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset 0 0 0 0 0 enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue
    (query 4, query 5, query 6, query 7, query 8) = (1, byteValue, 0, 0, 0) ∧
    (query 9, query 10, query 11, query 12, query 13, query 14) =
      (enabledCount, admittedApicId, seen0, seen1, seen2, seen3) := by
  simp [byteStepQuery] at accepted ⊢
  repeat' (split at accepted <;> (try simp_all))

/-- Every completed record past its header clears all partial fields,
including non-processor records between local-APIC entries. -/
theorem completed_record_clears_partial_state
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64)
    (pastLength : recordOffset ≠ 1) (nonempty : recordLength ≠ 0)
    (complete : recordOffset + 1 = recordLength)
    (field : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 ∨ word = 8) :
    byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word = 0 := by
  rcases field with h | h | h | h | h <;> subst word <;>
    simp [byteStepQuery, pastLength, nonempty, complete]

/-- A successful kind-byte transition admits only the four supported record
kinds, providing the premise required by the length-byte framing proof. -/
theorem record_kind_supported
    (currentOffset enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (accepted : byteStepQuery currentOffset 0 0 0 0 0 enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue 2 = 0) :
    byteValue = 0 ∨ byteValue = 1 ∨ byteValue = 2 ∨ byteValue = 4 := by
  apply Classical.byContradiction
  intro unsupported
  simp only [not_or] at unsupported
  simp [byteStepQuery, unsupported.1, unsupported.2.1,
    unsupported.2.2.1, unsupported.2.2.2] at accepted
  split at accepted <;> simp_all

/-- The length byte must match the retained supported kind. A successful
header retains that actual byte and advances to the first payload byte. -/
theorem record_length_retained
    (currentOffset kind enabledCount admittedApicId seen0 seen1 seen2 seen3
      tableLength executingApicId byteOffset byteValue : UInt64)
    (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 4)
    (accepted : byteStepQuery currentOffset 1 kind 0 0 0 enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset 1 kind 0 0 0 enabledCount admittedApicId
      seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue
    byteValue = (if kind = 0 then 8 else if kind = 1 then 12 else if kind = 2 then 10 else 6) ∧
    (query 4, query 5, query 6, query 7, query 8) = (2, kind, byteValue, 0, 0) ∧
    (query 9, query 10, query 11, query 12, query 13, query 14) =
      (enabledCount, admittedApicId, seen0, seen1, seen2, seen3) := by
  rcases supported with h | h | h | h <;> subst kind <;>
    simp [byteStepQuery] at accepted ⊢
  all_goals repeat' (split at accepted <;> (try simp_all))

/-- Between the length byte and completion, successful payload transitions
preserve the retained framing and advance the record offset by exactly one. -/
theorem payload_preserves_framing
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (pastKind : recordOffset ≠ 0) (pastLength : recordOffset ≠ 1)
    (incomplete : recordOffset + 1 ≠ recordLength)
    (accepted : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 = 0) :
    let query := byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue
    (query 4, query 5, query 6) = (recordOffset + 1, recordKind, recordLength) := by
  simp [byteStepQuery, pastKind, pastLength, incomplete] at accepted ⊢
  repeat' (split at accepted <;> (try simp_all))

/-- Terminal status implies zero error and the final byte position. -/
theorem terminal_byte_has_no_error
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (terminal : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 1 = 3) :
    byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 = 0 ∧ byteOffset + 1 = tableLength := by
  change (if byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 != 0 then 2
    else if byteOffset + 1 == tableLength then 3 else 1) = (3 : UInt64) at terminal
  split at terminal
  · contradiction
  · rename_i good
    simp only [bne_iff_ne] at good
    split at terminal
    · rename_i lastByte
      exact ⟨Classical.byContradiction good, by simpa only [beq_iff_eq] using lastByte⟩
    · contradiction

/-- Terminal success reports exactly four processors in the returned state. -/
theorem terminal_byte_count
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (terminal : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 1 = 3) :
    byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 9 = 4 := by
  have success := terminal_byte_has_no_error currentOffset recordOffset recordKind
    recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
    tableLength executingApicId byteOffset byteValue terminal
  let kind := if recordOffset == 0 then byteValue else recordKind
  let width := if recordOffset == 1 then byteValue else recordLength
  let complete := width != 0 && recordOffset + 1 == width
  let bits := if kind == 0 && recordOffset >= 4 then
    flags ||| (byteValue <<< ((recordOffset - 4) * 8)) else flags
  let count := if complete && kind == 0 && (bits &&& 1) != 0 then
    enabledCount + 1 else enabledCount
  change (if byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 != 0 then 0 else count) = 4
  rw [success.1]
  change count = 4
  have noError := success.1
  have lastByte := success.2
  clear terminal success
  simp only [byteStepQuery] at noError
  simp at noError
  have peel {condition : Prop} [Decidable condition] (bad rest : UInt64)
      (nonzero : bad ≠ 0) (ok : (if condition then bad else rest) = 0) :
      ¬condition ∧ rest = 0 := by
    split at ok
    · exact False.elim (nonzero ok)
    · exact ⟨by assumption, ok⟩
  obtain ⟨_, noError⟩ := peel 69 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 70 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 71 _ (by decide) noError
  obtain ⟨notTruncated, noError⟩ := peel 72 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 73 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 74 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 77 _ (by decide) noError
  obtain ⟨countChecked, _⟩ := peel 75 _ (by decide) noError
  have completed : complete = true := by
    simpa [complete, width, lastByte] using notTruncated
  have checked : ¬((byteOffset + 1 = tableLength ∧ complete = true) ∧ count ≠ 4) := by
    simpa [count, complete, width, kind, bits] using countChecked
  exact Classical.byContradiction (fun wrong => checked ⟨⟨lastByte, completed⟩, wrong⟩)

/-- Terminal success cannot leave any partial record fields behind. -/
theorem terminal_byte_clears_record
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64)
    (terminal : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 1 = 3)
    (projection : word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 ∨ word = 8) :
    byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word = 0 := by
  have success := terminal_byte_has_no_error currentOffset recordOffset recordKind
    recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
    tableLength executingApicId byteOffset byteValue terminal
  have noError := success.1
  have lastByte := success.2
  clear terminal success
  simp only [byteStepQuery] at noError
  simp at noError
  have peel {condition : Prop} [Decidable condition] (bad rest : UInt64)
      (nonzero : bad ≠ 0) (ok : (if condition then bad else rest) = 0) :
      ¬condition ∧ rest = 0 := by
    split at ok
    · exact False.elim (nonzero ok)
    · exact ⟨by assumption, ok⟩
  obtain ⟨_, noError⟩ := peel 69 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 70 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 71 _ (by decide) noError
  obtain ⟨notTruncated, _⟩ := peel 72 _ (by decide) noError
  have complete : (if recordOffset = 1 then byteValue else recordLength) ≠ 0 ∧
      recordOffset + 1 = (if recordOffset = 1 then byteValue else recordLength) := by
    simpa [lastByte] using notTruncated
  rcases projection with h | h | h | h | h <;> subst word <;>
    simp [byteStepQuery, complete.1, complete.2]

/-- Terminal success binds the executing CPU and returned admitted ID to
BSP zero, using the actual final error checks and returned projection. -/
theorem terminal_byte_bsp
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue : UInt64)
    (terminal : byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 1 = 3) :
    executingApicId = 0 ∧ byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 10 = 0 := by
  have success := terminal_byte_has_no_error currentOffset recordOffset recordKind
    recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3
    tableLength executingApicId byteOffset byteValue terminal
  let kind := if recordOffset == 0 then byteValue else recordKind
  let width := if recordOffset == 1 then byteValue else recordLength
  let complete := width != 0 && recordOffset + 1 == width
  let bits := if kind == 0 && recordOffset >= 4 then
    flags ||| (byteValue <<< ((recordOffset - 4) * 8)) else flags
  let id := if kind == 0 && recordOffset == 3 then byteValue else apicId
  let admitted := if complete && kind == 0 && (bits &&& 1) != 0 && enabledCount == 0 then
    id else admittedApicId
  change executingApicId = 0 ∧
    (if byteStepQuery currentOffset recordOffset recordKind recordLength
      apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue 2 != 0 then 0 else admitted) = 0
  rw [success.1]
  change executingApicId = 0 ∧ admitted = 0
  have noError := success.1
  have lastByte := success.2
  clear terminal success
  simp only [byteStepQuery] at noError
  simp at noError
  have peel {condition : Prop} [Decidable condition] (bad rest : UInt64)
      (nonzero : bad ≠ 0) (ok : (if condition then bad else rest) = 0) :
      ¬condition ∧ rest = 0 := by
    split at ok
    · exact False.elim (nonzero ok)
    · exact ⟨by assumption, ok⟩
  obtain ⟨_, noError⟩ := peel 69 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 70 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 71 _ (by decide) noError
  obtain ⟨notTruncated, noError⟩ := peel 72 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 73 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 74 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 77 _ (by decide) noError
  obtain ⟨_, noError⟩ := peel 75 _ (by decide) noError
  obtain ⟨bspChecked, _⟩ := peel 76 _ (by decide) noError
  have completed : complete = true := by
    simpa [complete, width, lastByte] using notTruncated
  have checked : ¬((byteOffset + 1 = tableLength ∧ complete = true) ∧
      (executingApicId ≠ 0 ∨ admitted ≠ 0)) := by
    simpa [admitted, complete, width, kind, bits, id] using bspChecked
  simpa [lastByte, completed] using checked

/-- Unsupported projection indices never expose state, for any caller inputs. -/
theorem byte_step_out_of_range
    (currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue word : UInt64) (outside : word > 15) :
    byteStepQuery currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue word = 0 := by
  simp only [byteStepQuery, outside, ↓reduceIte]

/-- The version word is independent of input validity and transition state. -/
theorem byte_step_version
    (currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue : UInt64) :
    byteStepQuery currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue 0 = 1 := by
  simp [byteStepQuery]

@[export leanos_qotom_madt_stream_byte_step_query]
def exportedByteStepQuery
    (currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue word : UInt64) : UInt64 :=
  byteStepQuery currentOffset recordOffset recordKind recordLength apicId flags enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength executingApicId byteOffset byteValue word

/-- Bind a terminal stream state to a same-CPU architectural observation.
The caller must pass the actual terminal result of an initialized byte stream;
scalar words alone cannot prove their own provenance. Status 1 is candidate
only. Status 2 rejects malformed/incomplete stream state or scalar widths;
status 5 carries the existing bootstrap error ordering. -/
def finishQuery
    (status error offset recordOffset recordKind recordLength apicId flags
      count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId word : UInt64) : UInt64 :=
  if word == 0 then 1
  else if word > 4 then 0
  else
    let streamInvalid := status != 3 || error != 0 || offset != tableLength ||
      tableLength <= 44 || tableLength > UInt64.ofNat maxAcpiSdtBytes ||
      recordOffset != 0 || recordKind != 0 || recordLength != 0 ||
      apicId != 0 || flags != 0 || count != 4 || admitted != 0 ||
      seen0 != 85 || seen1 != 0 || seen2 != 0 || seen3 != 0 || executing != 0
    let boundsError := if cpuidEdx > 0xffffffff then 306
      else if available > 1 then 307 else if sampleId > 0xffffffff then 308 else 0
    let bindingError := if available == 0 then 1
      else if cpuidEdx &&& 0x220 != 0x220 then 2
      else if sampleId != executing then 3
      else if apicBase &&& 0x100 == 0 then 4
      else if apicBase != QotomBspTopology.expectedApicBase then 5 else 0
    if streamInvalid || boundsError != 0 then
      if word == 1 then 2 else if word == 2 then
        if streamInvalid then 78 else boundsError
      else 0
    else if bindingError != 0 then
      if word == 1 then 5 else if word == 2 then bindingError else 0
    else if word == 1 then 1
    else if word == 2 then executing
    else if word == 3 then count
    else apicBase

/-- Acceptance requires the complete terminal shape and BSP observation, for
all scalar inputs. This does not establish the provenance of those inputs. -/
theorem finish_acceptance_requires
    (status error offset recordOffset recordKind recordLength apicId flags
      count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId : UInt64)
    (accepted : finishQuery status error offset recordOffset recordKind recordLength
      apicId flags count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId 1 = 1) :
    status = 3 ∧ error = 0 ∧ offset = tableLength ∧
    44 < tableLength ∧ tableLength ≤ UInt64.ofNat maxAcpiSdtBytes ∧
    recordOffset = 0 ∧ recordKind = 0 ∧ recordLength = 0 ∧
    apicId = 0 ∧ flags = 0 ∧ count = 4 ∧ admitted = 0 ∧
    seen0 = 85 ∧ seen1 = 0 ∧ seen2 = 0 ∧ seen3 = 0 ∧ executing = 0 ∧
    cpuidEdx ≤ 0xffffffff ∧ sampleId ≤ 0xffffffff ∧
    available = 1 ∧ cpuidEdx &&& 0x220 = 0x220 ∧ sampleId = executing ∧
    apicBase = QotomBspTopology.expectedApicBase := by
  simp [finishQuery] at accepted
  repeat' (split at accepted <;> (try simp_all))
  all_goals
    by_cases hav : available = 0 <;> simp_all
    by_cases hfeatures : cpuidEdx &&& 0x220 = 0x220 <;> simp_all
    by_cases hid : sampleId = 0 <;> simp_all
    by_cases hbsp : apicBase &&& 0x100 = 0 <;> simp_all
    by_cases hbase : apicBase = QotomBspTopology.expectedApicBase <;> simp_all
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj] at *
    simp at *
    omega


/-- Exact scalar acceptance contract. It describes the checked values, not
how the caller obtained them or whether application processors are dormant. -/
theorem finish_acceptance_iff
    (status error offset recordOffset recordKind recordLength apicId flags
      count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId : UInt64)
    : finishQuery status error offset recordOffset recordKind recordLength
      apicId flags count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId 1 = 1 ↔
    status = 3 ∧ error = 0 ∧ offset = tableLength ∧
    44 < tableLength ∧ tableLength ≤ UInt64.ofNat maxAcpiSdtBytes ∧
    recordOffset = 0 ∧ recordKind = 0 ∧ recordLength = 0 ∧
    apicId = 0 ∧ flags = 0 ∧ count = 4 ∧ admitted = 0 ∧
    seen0 = 85 ∧ seen1 = 0 ∧ seen2 = 0 ∧ seen3 = 0 ∧ executing = 0 ∧
    cpuidEdx ≤ 0xffffffff ∧ sampleId ≤ 0xffffffff ∧
    available = 1 ∧ cpuidEdx &&& 0x220 = 0x220 ∧ sampleId = executing ∧
    apicBase = QotomBspTopology.expectedApicBase := by
  constructor
  · exact finish_acceptance_requires status error offset recordOffset recordKind recordLength
      apicId flags count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId
  · intro valid
    have bsp : (4276095232 : UInt64) &&& 256 ≠ 0 := by decide
    have low : ¬tableLength ≤ 44 := by
      have h := valid.2.2.2.1
      exact UInt64.not_le.mpr h
    have high : ¬UInt64.ofNat maxAcpiSdtBytes < tableLength := by
      have h := valid.2.2.2.2.1
      exact UInt64.not_lt.mpr h
    simp_all [finishQuery, QotomBspTopology.expectedApicBase]

/-- For a complete terminal shape, widening a typed BSP observation preserves
exactly the existing typed bootstrap predicate. The topology witness is supplied
by the caller; this theorem does not construct it from scalar state. -/
theorem finish_typed_observation_iff
    (topology : QotomBspTopology.Witness)
    (observation : QotomBspTopology.BootstrapObservation)
    (length : UInt64) (low : 44 < length)
    (high : length ≤ UInt64.ofNat maxAcpiSdtBytes) :
    finishQuery 3 0 length 0 0 0 0 0 4 0 85 0 0 0 length 0
      observation.cpuidEdx.toUInt64 (if observation.readAvailable then 1 else 0)
      observation.apicBase observation.executingId.toUInt64 1 = 1 ↔
    QotomBspTopology.BootstrapValid topology observation := by
  have widened_bound (value : UInt32) : value.toUInt64 ≤ 0xffffffff := by
    have bound := value.toNat_lt
    simp only [UInt64.le_iff_toNat_le]
    simp
    omega
  rw [finish_acceptance_iff]
  simp only [QotomBspTopology.BootstrapValid, topology.matchesBaseline]
  simp [low, high, widened_bound, QotomBspTopology.baseline]
  simp only [← UInt64.toNat_inj, ← UInt32.toNat_inj]
  simp

/-- With a caller-supplied topology witness, scalar finish acceptance is
exactly success of the existing typed bootstrap binder on the same observation. -/
theorem finish_typed_binding_iff
    (topology : QotomBspTopology.Witness)
    (observation : QotomBspTopology.BootstrapObservation)
    (length : UInt64) (low : 44 < length)
    (high : length ≤ UInt64.ofNat maxAcpiSdtBytes) :
    finishQuery 3 0 length 0 0 0 0 0 4 0 85 0 0 0 length 0
      observation.cpuidEdx.toUInt64 (if observation.readAvailable then 1 else 0)
      observation.apicBase observation.executingId.toUInt64 1 = 1 ↔
    ∃ witness, QotomBspTopology.bindBootstrap topology observation = .ok witness := by
  rw [finish_typed_observation_iff topology observation length low high,
    QotomBspTopology.bootstrap_acceptance_iff_valid]

@[export leanos_qotom_madt_stream_finish_query]
def exportedFinishQuery
    (status error offset recordOffset recordKind recordLength apicId flags
      count admitted seen0 seen1 seen2 seen3 tableLength executing
      cpuidEdx available apicBase sampleId word : UInt64) : UInt64 :=
  finishQuery status error offset recordOffset recordKind recordLength apicId flags
    count admitted seen0 seen1 seen2 seen3 tableLength executing
    cpuidEdx available apicBase sampleId word

/-! ### Production root/copy/publication gate -/

/-- Bind the successful Qotom consumer result to the authoritative root-copy
pipeline before production publishes a topology identity.  The consumer uses
zero for success, unlike the older singleton stream's status-one convention.
Keeping that translation here prevents the C caller from replacing rejected
consumer fields with an accepted singleton-shaped tuple.

Result words are ABI/status/error/admitted APIC ID.  Errors 80 through 86 name
root binding, incomplete copy sequence, non-unique MADT, rejected consumer,
executing-CPU mismatch, inventory mismatch, and APIC-base mismatch. -/
def machineTopologyAdmissionResultQuery
    (selectedKind selectedAddress copiedRootAddress advertisedCount
      completedCopies madtCount consumerStatus consumerDetail admittedApicId
      processorCount apicBase executingApicId word : UInt64) : UInt64 :=
  let error :=
    if (selectedKind != 1 && selectedKind != 2) || selectedAddress == 0 ||
        copiedRootAddress != selectedAddress then 80
    else if advertisedCount == 0 ||
        advertisedCount > UInt64.ofNat maxAcpiRootEntries ||
        completedCopies != advertisedCount then 81
    else if madtCount != 1 then 82
    else if consumerStatus != 0 || consumerDetail != 0 then 83
    else if admittedApicId > 255 || admittedApicId != executingApicId ||
        admittedApicId != 0 then 84
    else if processorCount != 4 then 85
    else if apicBase != QotomBspTopology.expectedApicBase then 86
    else 0
  if word == 0 then 1
  else if word == 1 then if error == 0 then 1 else 2
  else if word == 2 then error
  else if word == 3 && error == 0 then admittedApicId
  else 0

@[export leanos_qotom_machine_topology_admission_result_query]
def exportedMachineTopologyAdmissionResultQuery
    (selectedKind selectedAddress copiedRootAddress advertisedCount
      completedCopies madtCount consumerStatus consumerDetail admittedApicId
      processorCount apicBase executingApicId word : UInt64) : UInt64 :=
  machineTopologyAdmissionResultQuery selectedKind selectedAddress
    copiedRootAddress advertisedCount completedCopies madtCount consumerStatus
    consumerDetail admittedApicId processorCount apicBase executingApicId word

theorem machine_topology_admission_exact_state_accepted :
    machineTopologyAdmissionResultQuery 2 0xb979f078 0xb979f078 10 10 1
      0 0 0 4 QotomBspTopology.expectedApicBase 0 1 = 1 := by
  native_decide

theorem machine_topology_admission_rejected_consumer_rejected :
    machineTopologyAdmissionResultQuery 2 0xb979f078 0xb979f078 10 10 1
      4 22 0 4 QotomBspTopology.expectedApicBase 0 2 = 83 := by
  native_decide

theorem machine_topology_admission_substituted_count_rejected :
    machineTopologyAdmissionResultQuery 2 0xb979f078 0xb979f078 10 10 1
      0 0 0 1 QotomBspTopology.expectedApicBase 0 2 = 85 := by
  native_decide

theorem machine_topology_admission_wrong_base_rejected :
    machineTopologyAdmissionResultQuery 2 0xb979f078 0xb979f078 10 10 1
      0 0 0 4 0xfee00000 0 2 = 86 := by
  native_decide

end LeanOS.QotomMadtStream
