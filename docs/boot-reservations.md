# Boot-owned frame reservations

`LeanOS.BootReservation` overlays a finite, checked manifest on the normalized
Multiboot2 memory map before `FrameAllocator.init`. Reservations always win
over firmware-usable memory. Byte ranges are half-open; validation rounds both
ends outward to 4 KiB frames and rejects zero length, 64-bit overflow, missing
or duplicate identities, out-of-policy physical addresses, and inconsistent
containment before any allocator state is returned.

The vocabulary covers low-memory policy, the complete loaded ELF/BSS image,
page tables, descriptor tables (GDT/IDT/TSS), other kernel stacks, the ordinary
privilege-entry guard and usable stack as distinct identities, embedded user
images/stacks, and the live Multiboot2 information block.
The overlapping in-image entries make the reviewable inventory explicit. The
Multiboot2 entry is bootstrap-lifetime data; this slice conservatively keeps it
reserved. Reclamation requires a separate proved transition after its last
reader.

Allocator initialization additionally requires the ordinary-entry guard to be
immediately below the ordinary-entry stack after frame rounding. Both must be
disjoint from page-table, descriptor-table, other-kernel-stack, and embedded-user
reservations. They intentionally remain contained by the enclosing loaded-image
reservation, which is an inventory parent rather than an independent object.

The Lean model proves deterministic initialization and carries checked
witnesses for nonempty normalized output, unconditional reservation precedence,
ordinary-entry separation, the normalized firmware map's usable-frame soundness,
and allocator acceptance. The allocator theorem
shows a successful allocation selected an initially free frame; precedence
therefore excludes every manifested reservation. Executable examples cover an
image inside usable RAM, touching/overlapping reservations, an unaligned
Multiboot2 block, usable RAM after the image, full consumption, and atomic
manifest rejection.

## Trusted boundary

Lean does not prove the linker, loader, Multiboot2 producer, assembly, compiler,
or hardware. `boot/linker.ld` is authoritative for the page-aligned half-open
`__boot_image_start`/`__boot_image_end` range. The image-policy script checks
those ELF symbols, their ordering/alignment, and containment of named static
boot artifacts. A future runtime adapter must populate the checked manifest
from these linker symbols and the validated Multiboot2 address and size; that
correspondence remains a reviewed TCB assumption. No `unsafe`, FFI, proof
escape, axiom, or constant is introduced by this model.
