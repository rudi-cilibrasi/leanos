# Optional early boot text console

The early console mirrors the same characters sent to COM1. It accepts an
explicit Multiboot2 EGA text surface at physical `0xb8000`, with 16-bit cells,
1–160 columns, 1–64 rows, and an even byte pitch between twice the column count
and 512. Other formats, addresses, missing tags and malformed metadata leave
serial output available without screen writes. It does not detect a monitor,
read EDID, program a video mode, or probe arbitrary framebuffer addresses.

The [Multiboot2 framebuffer information contract](https://www.gnu.org/software/grub/manual/multiboot2/html_node/Boot-information-format.html)
defines type 2 as EGA text, dimensions in characters and pitch in bytes.
The image's [optional console header](https://www.gnu.org/software/grub/manual/multiboot2/html_node/Console-header-tags.html)
advertises text support without requiring a display. The bounded tag walk
checks the whole aligned chain, rejects duplicate surfaces and stops at the
terminal tag. It reads at most the existing 64 KiB handoff bound inside the
initial 16 MiB mapping. The framebuffer address is never dereferenced during
parsing or geometry selection.

`BootTextConsole.checkRaw` exports the geometry selector to freestanding C.
Its proofs establish accepted geometry and that every character's two bytes
fit both the advertised surface extent and the 32 KiB color-text aperture,
without wrapped arithmetic. The C writer uses fixed cursor state and bounded
loops; it clears only character cells, preserving pitch padding. CR returns to
the start of the row. LF advances one row. Printing beyond the right edge wraps
on the next printable character, and advancing past the last row scrolls.
This avoids an extra blank line after an exactly full line followed by LF.
Long output wraps and scrolls with constant buffer use. Nonprintable bytes
other than CR/LF display as `?`; serial bytes remain unchanged.

The capability is borrowed only during initial boot. It depends on the
bootloader's advertised surface, the existing initial identity map and working
legacy text decode. The display sink is disabled before PCI quarantine can
remove that decode and before allocation or root changes. Consequently, the
J1900 CPU diagnostic's BOOT/CPU/CONTROL/FINAL records can remain visible, but
later q35 records are serial-only. Supporting display output past quarantine
needs a separately admitted device/mapping lifetime; this change grants none.
Earliest assembly failures are also serial-only. The backend never calls the
serial logger and skips reentrant screen writes.

The Qotom FADT previously reported `NO_VGA`, while its monitor displayed GRUB.
That observation alone does not justify writing a fixed VGA address. This path
requires GRUB to explicitly advertise an EGA text surface; the actual Qotom
handoff and visible result still need physical verification. A graphics-only
handoff remains unsupported and requires a bounded framebuffer backend to
finish issue #335. No Qotom screen result is claimed by hosted or QEMU tests.

`python3 scripts/test-boot-text-console.py` checks malformed and truncated tags,
duplicate/absent/unsupported displays, full-width scalar rejection, exact-width
lines, CR/LF, scrolling, long output, reentrancy, disabled output, and guarded
memory including pitch padding. It executes the generated selector with the
writer under ordinary and ASan/UBSan builds, and separately checks that the
freestanding selector links without runtime dependencies. Image and physical
validation remain separate requirements.
