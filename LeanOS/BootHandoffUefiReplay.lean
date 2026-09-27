import LeanOS.BootMemoryMapStreamAuthority

/-!
# UEFI GRUB handoff replay

A bounded replay of the exported version-five handoff walker over a
UEFI-GRUB-shaped Multiboot2 stream. It lives outside
`LeanOS.BootMemoryMapStreamAuthority` so the replay's list constants never
enter that module's generated boundary C.
-/
namespace LeanOS.BootHandoffUefiReplay
open LeanOS.BootMemoryMapStreamAuthority

/-! ## UEFI GRUB tag order

GRUB `x86_64-efi` emits the EFI memory map (tag 17) directly after the new
RSDP (tag 15); BIOS GRUB ends with the ACPI tags. This handoff has that shape:
a one-entry map, tag 14 and tag 15 naming distinct RSDTs (OVMF publishes
separate ACPI 1.0 and 2.0 table sets), tag 17, and the end tag. The exported
walker must admit it and select the XSDT. -/

def replayWordsV5 (address extent : UInt64) (words : List UInt64) :
    Array UInt64 := Id.run do
  let queries := (List.range 41).toArray.map (·.toUInt64)
  let mut s := queries.map (initWordV5 0x36d76289 address extent 0)
  let mut offset : UInt64 := 0
  for chunk in words do
    let terminal : UInt64 := if offset + 8 == extent then 1 else 0
    s := queries.map fun q => stepWordV5 s[0]! s[1]! s[2]! s[3]! s[4]! s[5]!
      s[6]! s[7]! s[8]! s[9]! s[10]! s[11]! s[12]! s[13]! s[14]! s[15]! s[16]!
      s[17]! s[18]! s[23]! s[24]! s[25]! s[26]! s[27]! s[28]! s[29]! s[30]!
      s[31]! s[32]! s[33]! s[34]! s[35]! s[36]! s[37]! s[38]! address offset
      chunk terminal q
    offset := offset + 8
  return s

def uefiGrubHandoff : List UInt64 :=
  [0x98, 0x2800000006, 0x18, 0x0, 0x1000000, 0x1,
   0x1c0000000e, 0x2052545020445352, 0x205348434f42ac, 0x1fb7d000,
   0x2c0000000f, 0x2052545020445352, 0x2205348434f4236, 0x241fb7d074,
   0x1fb7d0e8, 0x4e,
   0x1000000011, 0x100000030,
   0x800000000]

example :
    let s := replayWordsV5 0x37000 0x98 uefiGrubHandoff
    (s[1]!, s[2]!, s[39]!, s[40]!) = (complete, noError, acpiRootKindXsdt, 0x1fb7d0e8) := by
  native_decide

end LeanOS.BootHandoffUefiReplay
