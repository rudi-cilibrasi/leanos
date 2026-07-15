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

`classify` extends that user refinement with a finite privileged-access
context: CPL0/CPL3, read/write/execute, CR0.WP, EFER.NXE, CR4.SMEP/SMAP, and
the EFLAGS.AC override used for a bounded supervisor copy window. It conjoins
U/S and R/W across every ancestor and the leaf, and returns distinct failures
for non-presence, U/S, R/W, NX, SMEP, SMAP, malformed reserved bits, and frame
range. The reviewed `PolicyRegion` constructor describes supervisor read-only
executable kernel text; supervisor writable NX data, stacks, and page tables;
user read-only executable text; and user writable NX stacks. Pages and frames
are explicit policy inputs, never inferred ownership from linker addresses.

Machine-checked examples cover ancestor and leaf restrictions, every control
bit enabled and disabled, AC clear and set, malformed entries, and distinct
address-space values. Theorems establish W^X for every policy leaf and the
exact attributes of each region; executable classifications establish CPL3
confinement, WP write denial, SMEP execute denial, and SMAP's explicit copy
override. Disabling WP, SMEP, or SMAP deliberately supplies counterexamples to
those claims.

Machine-checked theorems prove structural validity, current frame ownership,
user-read agreement with `VirtualMapping.translate`, write-permission
non-amplification, NX enforcement, unmapped-page denial, and separation of
distinct frames across address spaces. Executable examples cover read-only
access, denied write, a handcrafted supervisor page, NX denial, a
non-canonical address, conflicting leaf values, and distinct address spaces.

The model assumes x86 effective permission conjunction, CR0.WP semantics,
NXE's control of NX, SMEP/SMAP and AC semantics, and no concurrent page-table
mutation during classification. The following remain trusted integration
responsibilities: correct CR3 selection and table physical addresses, hardware
interpretation of entry bits and reserved fields, EFER.NXE being enabled,
accessed/dirty-bit updates, TLB invalidation and coherence, page-fault delivery,
the compiler, boot assembly, and hardware. No theorem here concerns the boot
image or QEMU. The model adds no proof escape, FFI, or trusted declaration.

Virtual aliases are allowed only when the abstract state contains an explicit
mapping at each virtual page. Each mapping passes the existing capability and
ownership checks; the encoder cannot synthesize an alias.
