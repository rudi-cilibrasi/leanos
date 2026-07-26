# Boot-time frame allocation

The first boot allocation preserves the Multiboot2 magic and information
pointer across the 32-bit to 64-bit transition. Physical memory is copied into
a 64 KiB static buffer only through the generated version-two stream
transition, which binds the aligned identity, advertised extent, exact offset,
and terminal chunk. Multiboot2 alignment padding is not interpreted. The
generated version-three authority then accepts one version-zero memory-map tag
with at most 128 24-byte entries and rejects bad headers, tag advances, entry
layouts, duplicate or missing maps, zero lengths, reserved entry words, and
fixed-width overflow before exposing candidate authority.

Usable entries contribute only complete 4 KiB pages. Non-usable entries take
precedence independent of input order. The generated manifest boundary checks
the canonical nine reservation identities, including low memory, the complete
loaded image and its live subranges, and the copied handoff. Selection is
restricted to the 16 MiB bootstrap identity map. The selected page is fully
zeroed and checked before the generated publication transition exposes the
object identifier.

`LeanOS.BootMemoryMapStreamPipeline` is the rich proof-side composition from
the exact accepted byte sequence through `BootMemoryMapDecoder`,
`BootReservation.initializeAllocator`, and `FrameAllocator.allocate`. It proves
selected-frame usable soundness, the boot-accessible bound, and reservation
exclusion, and binds the complete decoded, normalized, reserved, and selected
projection. `LeanOS.BootAllocation` retains the allocator-to-scrub and
fresh-publication model theorems. The production final ELF rejects the legacy
`leanos_boot_allocation_check` scalar adapter; the hosted oracle instead
exercises the generated selection transition's accepted and rejected cases.

The version-seven serial protocol records handoff acceptance, a stable bounded
map summary, the selected firmware-usable and unreserved frame, completed
scrub, publication, stale-object denial, and final status in exact order.
`scripts/run-image.sh` checks the protocol under pinned one-vCPU q35/TCG boots
with 64 MiB and 128 MiB. Negative fixtures remove or reorder scrub evidence,
forge the map summary, and omit the allocation trace.

## Claims and trusted boundary

Lean proves properties of the typed normalization, reservation, allocator,
stream composition, lifetime, and scrub models. Hosted replay tests generated
code for the bounded rich projection and allocation-free scalar cases. QEMU
demonstrates the integrated artifact for fixed reported maps and a controlled
malformed-handoff rejection. Neither compilation nor QEMU execution verifies
the binary.

Physical-memory reads and scrub writes in `boot/kernel.c`, handoff register
preservation and ABI in `boot/boot.S`, linker symbols, generated C, compiler,
GRUB, Multiboot2 producer, QEMU, firmware truthfulness, and hardware are in the
TCB. The version-three scalar parser and manifest decision are not yet proved
extensionally equal to the rich decoder, normalizer, reservation overlay, and
complete projection. Focused hosted/freestanding corpus and QEMU checks narrow
that correspondence assumption; they do not prove it for arbitrary bytes. No
new Lean `unsafe`, `extern`, axiom, constant, or proof escape is introduced.
