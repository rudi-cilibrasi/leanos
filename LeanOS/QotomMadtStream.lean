import LeanOS.QotomBspTopology

/-! Allocation-free byte stream for the Qotom processor inventory candidate.

This consumes an independently envelope-validated MADT, starting at byte 44.
The caller must carry exactly the returned scalar state into the next call.
Status 3 establishes only completed processor inventory, not runtime admission.
Root/copy validation, BSP register binding, interrupt routing and AP dormancy
remain separate obligations. In particular, type-4 routing bytes are consumed
but not validated here.

The scalar layout mirrors the existing q35 stream; the q35 function is unchanged.
Errors 69--74 retain its framing/record/online-capable/duplicate meanings;
75 rejects a count other than four, 76 rejects executing ID other than zero,
and 77 rejects disabled, extra, or out-of-order processor records.
-/
namespace LeanOS.QotomMadtStream

open BootTopology

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

end LeanOS.QotomMadtStream
