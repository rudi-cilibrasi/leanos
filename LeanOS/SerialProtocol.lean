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
  ⟨23, ["BOOT", "CANCELED-HANDLE-DENIAL", "CANCELED-RECEIPT", "DISPATCH", "ENTER", "FINAL", "FRESH-SEND", "OFFER", "OFFER-DENIAL", "REPLACE", "REVOKE", "REVOKE-DENIAL", "UNRELATED"]⟩
]

/-- Every record identity, in family order. -/
def records : List (Nat × String) :=
  families.flatMap (fun family => family.tags.map (family.version, ·))

/-- The exact line prefix the guest prints for a record. -/
def prefixText (record : Nat × String) : String :=
  s!"LEANOS/{record.1} {record.2}"

/-- The C macro and shell variable name of a record. -/
def symbolName (record : Nat × String) : String :=
  s!"LEANOS_SERIAL_{record.1}_{record.2.replace "-" "_"}"

theorem family_versions_nodup : (families.map Family.version).Nodup := by decide
set_option maxRecDepth 32768 in
theorem records_nodup : records.Nodup := by decide
theorem families_nonempty : families.all (fun family => !family.tags.isEmpty) = true := by
  decide

end LeanOS.SerialProtocol
