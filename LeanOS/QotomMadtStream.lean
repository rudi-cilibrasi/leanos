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

def byteStepQuery
    (currentOffset recordOffset recordKind recordLength apicId flags
      enabledCount admittedApicId seen0 seen1 seen2 seen3 tableLength
      executingApicId byteOffset byteValue word : UInt64) : UInt64 :=
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
    (enabledCount >= 4 || nextApicId != enabledCount * 2 || !enabled)
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

end LeanOS.QotomMadtStream
