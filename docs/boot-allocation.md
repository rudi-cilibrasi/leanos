# Boot-time frame allocation

The first boot allocation preserves the Multiboot2 magic and information
pointer across the 32-bit to 64-bit transition. Physical memory is copied into
a 64 KiB static buffer only through the generated version-two stream
transition, which binds the aligned identity, advertised extent, exact offset,
and terminal chunk. Multiboot2 alignment padding is not interpreted. The
generated version-four authority then accepts one version-zero memory-map tag
with at most 64 total tags and 256 24-byte entries, deriving that entry bound
from the rich `BootMemoryMap.maxEntries` limit, and rejects bad headers,
tag advances, entry layouts, duplicate or missing maps, a 65th tag, zero
lengths, reserved entry words, and fixed-width overflow before exposing
candidate authority.

Usable entries contribute only complete 4 KiB pages. Non-usable entries take
precedence independent of input order. The generated manifest boundary checks
the canonical nine reservation identities, including low memory, the complete
loaded image and its live subranges, and the copied handoff. Selection is
restricted to the 16 MiB bootstrap identity map. The loaded-image and
Multiboot reservations must also end at or below that same physical limit; an
endpoint exactly at 16 MiB is accepted, while the first byte beyond it rejects
before selection. The selected page is fully zeroed and checked before the
generated publication transition exposes the object identifier.

`LeanOS.BootMemoryMapStreamPipeline` is the rich proof-side composition from
the exact accepted byte sequence through `BootMemoryMapDecoder`,
`BootReservation.initializeAllocator`, and `FrameAllocator.allocate`. It proves
selected-frame usable soundness, the boot-accessible bound, and reservation
exclusion, and binds the complete decoded, normalized, reserved, and selected
projection. `BootMemoryMapFullProjectionABI` executes that same exact rich
definition chain in hosted generated C and serializes every field of the
complete projection; its final ELF rejects retention of the separate scalar
decode/manifest/select/publication exports. The rich ELF is compiled twice
byte-for-byte and replays overlap-order, partial-page, unknown-type, duplicate,
maximum-entry, overflow, truncation, reservation-crossing, and output-mutation
cases. The boxed evaluator remains excluded from the allocation-free
production image. `BootMemoryMapScalarRichEquivalence` defines the canonical
fixed-width candidate encoding and proves, for arbitrary decoded entries,
checked intervals, and bounded frames, that
`leanos_boot_consume_exact_projection` accepts exactly the rich usable and
unreserved predicate. It also proves every accepted rich authority is
consumable through that export. `LeanOS.BootAllocation` retains the
allocator-to-scrub and
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
malformed-handoff rejection. The proof-side and freestanding exact-byte
65-tag fixture agree that the rich decoder and scalar ABI reject at their
respective `tooManyTags` errors. A separate exact-boundary theorem replays the
same usable handoff through the rich decoder/reservation/allocator chain and
the scalar production decision: both accept image and Multiboot endpoints at
16 MiB, and both reject either reservation beyond it. Generated freestanding C
fixtures cover the same positive and negative endpoints. Neither compilation
nor QEMU execution verifies the binary.

Physical-memory reads and scrub writes in `boot/kernel.c`, handoff register
preservation and ABI in `boot/boot.S`, linker symbols, generated C, compiler,
GRUB, Multiboot2 producer, QEMU, firmware truthfulness, and hardware are in the
TCB. The hosted rich ABI consumes the canonical decoder and full model exactly.
The freestanding image consumes its canonical scalar candidate encoding through
the sole generated exact-projection decision point; the former selector is
absent from focused and production final ELFs. QEMU requires the resulting
`projection=exact-rich` record before scrub and publication. Generated C, C
transport of the scalar words, compiler output, and machine execution remain
trusted/tested rather than proved refinement. No new Lean `unsafe`, `extern`,
axiom, constant, or proof escape is introduced.
