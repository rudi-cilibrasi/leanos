import LeanOS.BoundaryVocabulary

/-!
# Serial protocol vocabulary

The single Lean-owned list of the versioned serial records the boot images
emit and the runners expect.  A record identity is a protocol family version
and an upper-case tag; the guest prints it as the line prefix
`LEANOS/<version> <TAG>` and every field after the prefix is scenario data.
`leanos-oracle serial` emits this table; the build renders it into the
generated `serial-protocol.h` (one `LEANOS_SERIAL_<version>_<TAG>` string
macro per record, consumed by `boot/kernel.c` and `boot/boot.S` through
adjacent-literal concatenation, so the emitted bytes are unchanged) and the
generated `serial-protocol.sh` fragment (one shell variable per record,
sourced by the runner scripts and the fake-guest fixtures).  The theorems
below prove the family versions and record identities are unique; the
renderer rejects a malformed tag or a duplicate symbol, and it and the
consumers remain trusted integration steps.  Family 2 is intentionally absent: its transcript survives
only as a deliberately stale forgery inside the fake-guest fixture, and the
gate lets fixtures forge exactly those records that are not in this table.
-/
namespace LeanOS.SerialProtocol

structure Family where
  version : Nat
  tags : List String
  deriving Repr

def families : List Family := [
  ⟨3, ["FINAL", "ORACLE"]⟩,
  ⟨4, ["PROBE"]⟩,
  ⟨5, ["CONTEXT", "ENTRY", "FINAL", "RESUME", "SWITCH", "SYSCALL", "TIMER"]⟩,
  ⟨6, ["BOOT", "CLEANUP", "CONTROL", "COPY", "POLICY", "PROBE"]⟩,
  ⟨7, ["ALLOC", "BOOTALLOC", "HANDOFF", "MAP", "PUBLISH", "SCRUB"]⟩,
  ⟨8, ["NEGATIVE", "PAGING", "TERMINAL"]⟩,
  ⟨9, ["CAPREUSE", "RETURN"]⟩,
  ⟨10, ["BOOT", "FINAL", "IPC"]⟩,
  ⟨11, ["ENTRY-ADVERSARIAL", "ENTRY-HIGH-WATER", "ENTRY-STACK-OVERFLOW", "USER-FAULT"]⟩,
  ⟨13, ["BOOT", "EXTENDED-STATE", "FINAL"]⟩,
  ⟨14, ["BOOT", "DISPATCH", "ENTER", "FAST-ENTRY", "FAULT-ENTRY", "FINAL", "PEER", "PF-SNAPSHOT", "PF-TERMINAL", "PF-WALK", "TERMINATE"]⟩,
  ⟨15, ["DMA", "DMA-FUNCTION"]⟩,
  ⟨16, ["BOOT", "DIRECT-PORT-CANARY", "DIRECT-PORT-CONTROL", "DIRECT-PORT-DENIAL", "DIRECT-PORT-DISPATCH", "DIRECT-PORT-PEER", "DIRECT-PORT-TERMINATE", "ENTER", "FINAL"]⟩,
  ⟨17, ["BOOT", "ENTRY-MANIFEST", "NMI", "NMI-READY"]⟩,
  ⟨18, ["BOOT", "BREAKPOINT-DISPATCH", "BREAKPOINT-ENTRY", "BREAKPOINT-PEER", "BREAKPOINT-TERMINATE", "DIVIDE-ERROR-DISPATCH", "DIVIDE-ERROR-ENTRY", "DIVIDE-ERROR-PEER", "DIVIDE-ERROR-TERMINATE", "EARLY-TERMINAL", "EARLY64-READY", "ENTER", "FINAL"]⟩,
  ⟨19, ["BOOT", "ENTER", "FINAL", "TLB", "TLB-CPL3"]⟩,
  ⟨20, ["A-ALLOC", "A-REJECT", "B-ALLOC", "B-CONTEXT", "B-PUBLISH", "BOOT", "CANARY", "CLEANUP", "DISPATCH", "ENTER", "FINAL", "FRAME", "SCRUB", "STALE"]⟩,
  ⟨21, ["VTD", "VTD-ACTIVATE", "VTD-ASSIGN", "VTD-FAULT", "VTD-PLAN", "VTD-REUSE", "VTD-TABLES", "VTD-TRANSFER", "VTD-UNMAPPED-FAULT", "VTD-WRITE-FAULT"]⟩,
  ⟨22, ["ACCEPT", "BOOT", "DELEGATED-SEND", "DISPATCH", "ENTER", "EXCESS-RIGHT-DENIAL", "FINAL", "OFFER", "SEALED-DENIAL", "UNRELATED"]⟩,
  ⟨23, ["BOOT", "CANCELED-HANDLE-DENIAL", "CANCELED-RECEIPT", "DISPATCH", "ENTER", "FINAL", "FRESH-SEND", "OFFER", "OFFER-DENIAL", "REPLACE", "REVOKE", "REVOKE-DENIAL", "UNRELATED"]⟩,
  ⟨24, ["BOOT", "CPU", "CONTROL"]⟩,
  ⟨25, ["BOOT", "CPU", "CONTROL", "PCI-SCAN", "PCI-HEADER"]⟩
]

/-- Every record identity, in family order. -/
def records : List (Nat × String) :=
  families.flatMap (fun family => family.tags.map (family.version, ·))

/-- Exact production `LEANOS/3 FINAL` reasons that can be emitted before the
platform-admission boundary. Runtime fail-stop reasons are intentionally absent. -/
def preAdmissionRejectionReasons : List String := [
  "j1900-cpu-profile",
  "j1900-cpu-control-policy",
  "j1900-msr-readback",
  "qotom-platform-pending",
  "qotom-pci-enumeration",
  "dma-command-model",
  "dma-command-readback",
  "dma-empty-inventory",
  "dma-global-policy",
  "dma-identity",
  "dma-inventory",
  "dma-q35-nic-none",
  "dma-required-missing"
]

/-- Exact production `LEANOS/7 BOOTALLOC` reasons emitted by `handoff_fail`
before `boot_allocate` publishes its successful terminal. Keeping this
separate from `preAdmissionRejectionReasons` prevents a FINAL-only reason from
being relabeled as a BOOTALLOC rejection. -/
def preAdmissionBootallocRejectionReasons : List String := [
  "authority-init",
  "authority-rejected",
  "bounds",
  "decode-incomplete",
  "decode-init",
  "decode-rejected",
  "frame-budget-projection-authority",
  "frame-budget-unpublished-frame",
  "magic",
  "pointer",
  "projection-authority",
  "projection-entry",
  "projection-entry-count",
  "projection-mutation-raw-selection",
  "projection-terminal",
  "publication",
  "raw-selection-authority",
  "scrub",
  "stream-incomplete",
  "stream-init",
  "stream-step",
  "topology-admission-publication",
  "topology-admission-result",
  "topology-cpuid-apic",
  "topology-cpuid-leaf",
  "topology-handoff-length",
  "topology-madt-duplicate",
  "topology-madt-generated-entries",
  "topology-madt-generated-envelope",
  "topology-madt-missing",
  "topology-madt-selection",
  "topology-qotom-admission-result",
  "topology-qotom-bsp-consumer",
  "topology-qotom-cpuid-leaf",
  "topology-qotom-interrupt-window",
  "topology-qotom-madt-length",
  "topology-qotom-same-cpu",
  "topology-root-copy",
  "topology-root-entries",
  "topology-root-entry-address",
  "topology-root-entry-duplicate",
  "topology-root-entry-index",
  "topology-root-header",
  "topology-root-kind",
  "topology-root-selection",
  "topology-root-vector",
  "topology-root-width",
  "topology-sdt-address",
  "topology-sdt-address-space",
  "topology-sdt-address-width",
  "topology-sdt-checksum",
  "topology-sdt-envelope",
  "topology-sdt-length",
  "topology-sdt-window",
  "topology-table-copy-address",
  "topology-table-copy-binding",
  "topology-table-copy-budget",
  "topology-table-copy-error",
  "topology-table-copy-exposed",
  "topology-table-copy-final-cursor",
  "topology-table-copy-incomplete",
  "topology-table-copy-length",
  "topology-table-copy-next-byte",
  "topology-table-copy-offset",
  "topology-table-copy-partial-cursor",
  "topology-table-copy-sequence",
  "topology-table-copy-status",
  "topology-table-copy-stream",
  "topology-table-copy-terminal"
]

/-- Every scenario-specific BOOT identity emitted immediately after serial
initialization and before the platform-admission boundary. -/
def preAdmissionBootRecords : List (Nat × String) := [
  (17, "BOOT"),
  (22, "BOOT"),
  (23, "BOOT"),
  (20, "BOOT"),
  (14, "BOOT"),
  (13, "BOOT"),
  (19, "BOOT"),
  (16, "BOOT"),
  (18, "BOOT"),
  (6, "BOOT"),
  (10, "BOOT")
]

/-- Record identities that can be emitted after the scenario BOOT record but
before `boot_allocate` can produce a typed `BOOTALLOC` rejection. Repetition
is permitted in the capture (for example one DMA-FUNCTION per device); this
list owns only the finite identity vocabulary for that phase. -/
def preAdmissionPhaseRecords : List (Nat × String) := [
  (15, "DMA-FUNCTION"),
  (15, "DMA"),
  (8, "PAGING"),
  (19, "TLB"),
  (21, "VTD"),
  (21, "VTD-PLAN"),
  (21, "VTD-TABLES"),
  (21, "VTD-ASSIGN"),
  (21, "VTD-ACTIVATE")
]

/-- The exact line prefix the guest prints for a record. -/
def prefixText (record : Nat × String) : String :=
  s!"LEANOS/{record.1} {record.2}"

/-- The C macro and shell variable name of a record. -/
def symbolName (record : Nat × String) : String :=
  s!"LEANOS_SERIAL_{record.1}_{record.2.replace "-" "_"}"

theorem family_versions_nodup : (families.map Family.version).Nodup := by decide
set_option maxRecDepth 32768 in
theorem records_nodup : records.Nodup := by decide
theorem pre_admission_rejection_reasons_nodup :
    preAdmissionRejectionReasons.Nodup := by decide
theorem pre_admission_bootalloc_rejection_reasons_nodup :
    preAdmissionBootallocRejectionReasons.Nodup := by decide
theorem pre_admission_boot_records_nodup : preAdmissionBootRecords.Nodup := by
  decide
theorem pre_admission_boot_records_are_protocol_records :
    preAdmissionBootRecords.all (· ∈ records) = true := by
  decide
theorem pre_admission_phase_records_nodup : preAdmissionPhaseRecords.Nodup := by
  decide
theorem pre_admission_phase_records_are_protocol_records :
    preAdmissionPhaseRecords.all (· ∈ records) = true := by
  decide
theorem families_nonempty : families.all (fun family => !family.tags.isEmpty) = true := by
  decide

end LeanOS.SerialProtocol
