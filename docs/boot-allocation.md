# Boot-time frame allocation

The first boot allocation preserves the Multiboot2 magic and information
pointer across the 32-bit to 64-bit transition. A bounded, allocation-free C
parser accepts one version-zero memory-map tag with at most 128 24-byte entries
inside a 64 KiB, eight-byte-aligned handoff. It rejects bad magic, pointers,
bounds, tag advances, entry layouts, counts, zero lengths, and fixed-width
overflow before publishing state.

Usable entries contribute only complete 4 KiB pages. Non-usable entries take
precedence independent of input order. Low memory, the linker-defined complete
image, and the live handoff are then reserved. Selection is restricted to the
16 MiB bootstrap identity map. The selected page is fully zeroed and checked
before the object identifier is published.

`LeanOS.BootAllocation` is the fixed-width generated-code boundary. Its proof
connects successful allocator selection from `BootReservation` with the
existing frame-scrubbing ownership and fresh-publication theorems; rejection
is state preserving. The scalar evidence adapter additionally rejects missing
normalization, reservation, scrub, or publication stages. The shared oracle
exercises success, wrong magic, truncation, malformed layout, overflow, no
eligible frame, and publication before scrub in Lean, hosted generated code,
and the boot image.

The version-seven serial protocol records handoff acceptance, a stable bounded
map summary, the selected firmware-usable and unreserved frame, completed
scrub, publication, stale-object denial, and final status in exact order.
`scripts/run-image.sh` checks the protocol under pinned one-vCPU q35/TCG boots
with 64 MiB and 128 MiB. Negative fixtures remove or reorder scrub evidence,
forge the map summary, and omit the allocation trace.

## Claims and trusted boundary

Lean proves properties of the typed normalization, reservation, allocator,
lifetime, and scrub models. Hosted replay tests generated-code agreement for
the bounded scalar cases. QEMU demonstrates the integrated artifact for two
reported maps. Neither compilation nor QEMU execution verifies the binary.

The byte parser and physical-memory writes in `boot/kernel.c`, handoff register
preservation and ABI in `boot/boot.S`, linker symbols, generated C, compiler,
GRUB, Multiboot2 producer, QEMU, firmware truthfulness, and hardware are in the
TCB. The parser-to-model correspondence is a reviewed assumption tested by the
shared corpus; it is not a proof of arbitrary bytes. No new Lean `unsafe`,
`extern`, axiom, constant, or proof escape is introduced.
