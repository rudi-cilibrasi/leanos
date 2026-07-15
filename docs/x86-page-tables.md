# x86-64 page-table refinement model

`LeanOS.X86PageTable` is an executable refinement boundary between the current
virtual-mapping model and a deliberately small x86-64 page-table subset. It
supports 4 KiB pages, four levels, the lower canonical half, and physical frame
numbers below 2^40. Huge pages, upper-half user addresses, aliases created
outside explicit abstract mappings, and optional paging features are excluded.

The encoder independently rechecks canonicality, the live object-to-frame
binding, frame ownership, and representable physical range. It emits present
user leaves, preserves abstract writability, and marks every user leaf NX.
Every ancestor is present, user-accessible, and writable. Kernel pages are not
encoder inputs and a supervisor leaf is never produced.

Machine-checked theorems prove structural validity, current frame ownership,
user-read agreement with `VirtualMapping.translate`, write-permission
non-amplification, NX enforcement, unmapped-page denial, and separation of
distinct frames across address spaces. Executable examples cover read-only
access, denied write, a handcrafted supervisor page, NX denial, a
non-canonical address, conflicting leaf values, and distinct address spaces.

The following remain modeled ISA assumptions and trusted integration
responsibilities: correct CR3 selection and table physical addresses, hardware
interpretation of entry bits and reserved fields, EFER.NXE being enabled,
accessed/dirty-bit updates, TLB invalidation and coherence, page-fault delivery,
the compiler, boot assembly, and hardware. No theorem here concerns the boot
image or QEMU. The model adds no proof escape, FFI, or trusted declaration.

Virtual aliases are allowed only when the abstract state contains an explicit
mapping at each virtual page. Each mapping passes the existing capability and
ownership checks; the encoder cannot synthesize an alias.
