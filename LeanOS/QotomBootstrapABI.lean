import LeanOS.QotomBspTopology
import LeanOS.BootMemoryMapDecoderABI

/-! Bounded hosted boundary for the combined Qotom bootstrap candidate.
Status 1 means candidate only, never platform or runtime admission. -/
namespace LeanOS.QotomBootstrapABI

open QotomBspTopology

def topologyErrorCode : Error → UInt64
  | .unsupportedSource => 1
  | .unsupportedVersion => 2
  | .tooManyProcessors => 3
  | .duplicateApicId => 4
  | .noEnabledProcessor => 5
  | .wrongBsp => 6
  | .processorInventoryMismatch => 7

def bootstrapErrorCode : BootstrapError → UInt64
  | .unavailable => 1
  | .missingFeatures => 2
  | .executingIdMismatch => 3
  | .notBootstrapProcessor => 4
  | .unsupportedApicState => 5

private def failure (status code word : UInt64) : UInt64 :=
  if word == 1 then status else if word == 2 then code else 0

/-- Five words: version, status, ID/error, processor count, APIC-base value.
Status 2 preserves the existing root adapter's error projection; 4 is Qotom
inventory rejection and 5 is BSP binding rejection. New scalar bound errors
306..308 extend the existing adapter codes. No scalar is truncated unchecked.
The existing root query supplies its complete bounded decoder envelope; its
single-core policy result is not reused as Qotom candidate authority. -/
def query (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executingId cpuidEdx available apicBase sampleId word : UInt64) : UInt64 :=
  if word == 0 then 1
  else if word > 4 then 0
  else if cpuidEdx > 0xffffffff then failure 2 306 word
  else if available > 1 then failure 2 307 word
  else if sampleId > 0xffffffff then failure 2 308 word
  else
    let prior := BootMemoryMapDecoderABI.capturedRootQuery magic infoAddress info rootBytes
      rootAddress addresses tables executingId 1
    if prior == 2 then
      BootMemoryMapDecoderABI.capturedRootQuery magic infoAddress info rootBytes
        rootAddress addresses tables executingId word
    else if prior != 1 && prior != 3 then failure 2 309 word
    else
      match BootMemoryMapDecoder.AcpiRootDecoder.decode
          { magic := magic.toNat, infoAddress := infoAddress.toNat, bytes := info.data.toList } with
      | .error _ => failure 2 309 word
      | .ok tags =>
        let copies := (addresses.toList.zip tables.toList).map fun (address, bytes) =>
          ({ physicalAddress := address, bytes := bytes.data.toList } : BootTopology.CopiedAcpiSdt)
        match checkBootstrapAuthoritative tags
            { physicalAddress := rootAddress, bytes := rootBytes.data.toList } copies
            (UInt32.ofNat executingId.toNat)
            { cpuidEdx := UInt32.ofNat cpuidEdx.toNat, readAvailable := available == 1,
              apicBase, executingId := UInt32.ofNat sampleId.toNat } with
        | .error (.topology (.acpi reason)) =>
          failure 2 (BootTopology.authoritativeAcpiTopologyErrorCode reason) word
        | .error (.topology (.topology reason)) => failure 4 (topologyErrorCode reason) word
        | .error (.bootstrap reason) => failure 5 (bootstrapErrorCode reason) word
        | .ok witness =>
          if word == 1 then 1
          else if word == 2 then witness.bootstrap.observed.executingId.toUInt64
          else if word == 3 then witness.topology.observed.processors.length.toUInt64
          else witness.bootstrap.observed.apicBase

@[export leanos_qotom_bootstrap_query]
def exportedQuery (magic infoAddress : UInt64) (info rootBytes : ByteArray)
    (rootAddress : UInt64) (addresses : Array UInt64) (tables : Array ByteArray)
    (executingId cpuidEdx available apicBase sampleId word : UInt64) : UInt64 :=
  query magic infoAddress info rootBytes rootAddress addresses tables
    executingId cpuidEdx available apicBase sampleId word

theorem out_of_range_is_zero magic infoAddress info rootBytes rootAddress addresses tables
    executingId cpuidEdx available apicBase sampleId word (outside : word > 4) :
    query magic infoAddress info rootBytes rootAddress addresses tables
      executingId cpuidEdx available apicBase sampleId word = 0 := by
  have nonzero : word ≠ 0 := by
    intro zero
    subst word
    exact (by decide : ¬ ((0 : UInt64) > 4)) outside
  simp [query, nonzero, outside]

end LeanOS.QotomBootstrapABI
