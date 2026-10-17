# ADR 0024: Build-time admission of one subject ELF

- Status: Accepted, issue #492 (build-time half; the run-time half is the 2026-10-11 amendment)
- Date: 2026-10-10

## Context

Issue #492 asks for a loader subject that maps one pre-admitted, fixed ELF
from reserved frames into a fresh address space. That needs two halves:

1. **At build time**, decide which file may be loaded and with what
   segments, and put its bytes in reserved frames.
2. **At run time**, a ring-3 loader with a spawn capability creates a child
   and maps the admitted segments.

The run-time half needs a ring-3 spawn operation, and
[ADR 0010](0010-defer-fork.md) still gates that. This ADR covers the
build-time half only. It adds no syscall, no capability and no boot path
that reads the admitted bytes.

## Decision

### What is built

The example subject (`subjects/example`, built by the #484 rule) is also
linked as a separate static x86-64 executable. The rule uses the same
policy-checked relocatable object as slot C and links it with
`subjects/admitted.ld`. `scripts/build-subject.sh` then runs the Lean
checker `leanos-elf-admit` (`LeanOS.ElfAdmission.admit`) over the file and
writes the admitted plan. The build fails if the checker rejects the file.

Next, the file's bytes go into the slot object as section `.user.admitted`.
`boot/linker.ld` places that section page-aligned after the last subject
slot, in `[__user_admitted_start, __user_admitted_end)`. That range ends the
image and lies inside the embedded-user boot reservation. The kernel's boot
manifest (`BOOT_EMBEDDED_USERS_END` in `boot/kernel.c`) now ends that
reservation at `__user_admitted_end`, which matches the reservation the boot
page plan generator models (`__user_a_text_start` to `__boot_image_end`).

Only the `leanos-example-subject` image links the section. In every other
image the range is empty at the image end, so its layout does not change.
The example image's own layout grows by the file's pages; its plan check
was already `converge`.

No boot address space maps the range to ring 3. The boot page plan
classifies those pages as supervisor kernel data, as it does for any image
page outside the subject slots.

### The admission rules

`LeanOS.ElfAdmission.check` tests these reasons in order and reports the
first one that fails (`Rejection`):

| Reason | Rejected when |
| --- | --- |
| `truncatedHeader` | the file is shorter than the 64-byte ELF header |
| `badMagic`, `notElf64`, `notLittleEndian`, `badVersion` | the identity bytes are not ELF64, little-endian, version 1 |
| `notExecutable`, `wrongMachine` | the type is not `ET_EXEC`, or the machine is not x86-64 |
| `badHeaderLayout` | the header size is not 64 or the program-header entry size is not 56 |
| `tooManyProgramHeaders` | there are more than 8 program headers |
| `truncatedProgramHeaders` | the program-header table runs past the end of the file |
| `fileTooLarge` | the file is larger than 256 KiB |
| `unsupportedSegmentType` | a header is neither `PT_LOAD` nor a non-executable `PT_GNU_STACK` |
| `unknownSegmentFlags` | a header sets flag bits other than R, W and X |
| `noLoadSegment` | there is no `PT_LOAD` |
| `misalignedSegment` | a load segment's address or file offset is not page aligned |
| `writableExecutable` | a load segment is both writable and executable |
| `oversizeSegment` | a load segment is empty, larger than 64 KiB, or has more file bytes than memory bytes |
| `segmentOutsideFile` | a load segment's file bytes run past the end of the file |
| `outsideUserRange` | a load segment leaves the user window `[16 MiB, 18 MiB)` |
| `overlappingSegments` | two load segments share a page |
| `entryOutsideText` | the entry point is not in the file bytes of an executable load segment |

The user window starts at the first page the boot page plan does not map
(`userWindow_above_boot_plan`). Segments admitted there can therefore share
a future child address space with the boot mappings without aliasing them.

The admitted plan is the file's `PT_LOAD` headers, in file order. Each one
gives address, memory size, file offset, file size, and R/W/X. The plan also
records the entry point and the file size. `place` binds the plan to the
reserved range. That range must be page aligned and hold exactly the file
rounded up to a page, and it must lie inside the embedded-user reservation.
Each segment's physical source is then the range start plus its file
offset.

### Theorems

The theorems are in `LeanOS/ElfAdmission.lean`. They cover the plan, the
rejections, and the properties and placement of an admitted file.

**The plan:**

- `check_ok_iff` and `admit_plan_exact` show that a file is admitted exactly
  when no check fails. The plan is then exactly the projection above.

**Rejections:**

- `check_error_sound` shows that a reported rejection names a check that
  really fails.
- `check_total` and `Rejection.mem_all` show that every candidate is either
  admitted with its exact plan or rejected for a listed reason.

**Properties of an admitted file:**

- `admitted_header` covers the header checks.
- `admitted_program_headers_bounded` covers the program-header and file
  bounds.
- `admitted_program_header_types` covers the header types and flag bits.
- `admitted_segments_aligned` covers page alignment.
- `admitted_no_writable_executable` covers W^X.
- `admitted_segment_sizes` covers the size bounds.
- `admitted_segments_in_file` covers segments staying inside the file.
- `admitted_segments_in_user_window` covers the user window.
- `admitted_segments_disjoint` covers overlap.
- `admitted_entry_in_text` shows that the entry point lies in an executable,
  non-writable segment.

**Placement:**

- `placed_sources_reserved` shows that a placed plan keeps exactly the
  admitted segments. Every segment's source bytes are page aligned and lie
  inside the reserved range and the reservation.

### Build checks

`scripts/check-admitted-subject.py` runs after the example image's final
link. It requires the following:

- `.user_admitted` is exactly the reserved range.
- The section is read-only and non-executable.
- One identity `PT_LOAD` loads it from file bytes, so the boot loader puts
  those bytes at those frames.
- Its bytes equal the admitted file, byte for byte.
- The Lean checker, run again over the bytes read back from the image, gives
  the same plan and a valid placement.

It also mutates the real admitted file once for each reason the issue lists
and requires each copy to be rejected for that reason. Those reasons are:

- wrong machine
- not executable
- too many program headers
- misaligned segment
- W+X
- oversized segment
- outside the user range
- overlap
- entry outside text
- truncated header

Lean vectors in the module cover every reason through the byte parser.

## Trusted computing base

The checker is Lean code that the Lean kernel checks. It runs as a
host-compiled executable, so the Lean compiler and runtime that build
`leanos-elf-admit` are trusted for its verdicts. These are also trusted and
not proved:

- **ELF parsing assumptions.** `parse` reads ELF64 fields at the offsets the
  System V ABI gives. A wrong offset would make the checker reason about the
  wrong field. Nothing here proves those offsets against the specification.
  The encoder round-trip vector and the mutation vectors are tests of them,
  not proofs.
- **Placement.** The linker, `objcopy` and the boot loader are trusted to put
  exactly these bytes in these frames. The build re-reads the linked image to
  check this, but the boot loader's copy into RAM is not observed.
- **What admission does not cover.** Instruction content is covered by the
  #484 subject policy, and only for the relocatable object. Section headers
  are not covered, because the loader would read only program headers.
  Relocation is out: there is none to admit, because the file is `ET_EXEC`.

## Consequences

- The build-time half of #492 is in place. The run-time loader, the spawn
  operation it needs, and the theorems about the child's address space stay
  open, gated by ADR 0010.
- The example image carries the admitted file's pages. No other image
  changes.

## Amendment (2026-10-11): the run-time loader (#492)

ADR 0010's decision of 2026-10-10 and the ring-3 spawn syscall
(`LeanOS.SpawnSyscall`) unblock the run-time half. The `spawn-loader` image
adds it.

### What runs

Subject B is the loader. The kernel grants it spawn authority. Its read
authority is the reserved range `[__user_admitted_start, __user_admitted_end)`.
That range holds the admitted bytes of `subjects/loaded`, a subject built only
as an admitted executable: its manifest slot is `admitted`, so no slot of the
image links it. The kernel reads the admitted segments from those bytes'
program headers at boot. `scripts/check-admitted-subject.py` checks at build
time that the bytes are the file the checker admitted, with that plan.

B spawns a child and gives it a frame (syscalls 100 to 104). It asks the
kernel to load each admitted segment (105: the control word, the segment's
index, and the source address B claims). It then starts the child (106) and
waits for the child's word (107). The kernel runs the child on the child's
fresh root, at the admitted entry. The child sends one word through the one
endpoint capability spawn gave it. B is woken with that word and terminates
the child.

### Decision: map read-only segments, copy writable ones

- **A read-only segment is mapped in place.** Each of its pages is the
  reserved page holding its file bytes, mapped user, read-only, and
  executable only if admitted. The bytes cannot change, so sharing them is
  safe, and the child is charged no frame. A mapped page cannot provide a
  zero fill, so such a segment is accepted only when its memory image equals
  its file image. The bytes after the segment's end in its last page are the
  admitted file's following bytes or the range's zero padding, never anything
  outside the reserved range.
- **A writable segment is copied** into the frames the parent gave the child:
  the segment's file bytes, then zeros. It is mapped user, writable and
  no-execute. A child that writes its data never changes the admitted bytes,
  and the zero fill (bss) is exact.

The reserved range becomes user-visible, read-only, only in a loaded child's
own root. No boot address space maps it to ring 3.

### Model and theorems

`LeanOS.ChildLoader` models the child's pages as the kernel builds them.

| Property | Theorems |
| --- | --- |
| After loading, the child holds exactly the admitted segments with the admitted permissions | `step_preserves_exact`, `exact_rollback`, `started_exact`, `started_exact_unique` (SC-LOADER-EXACT) |
| The loader cannot map anything outside the reserved range | `step_preserves_inside`, `inside_rollback`, `load_outside_authority_rejected` (SC-LOADER-RESERVED-RANGE) |
| Any failure rolls back the spawn | `rejection_rolls_back`, `rollback_empty`, `refused_unchanged` (SC-LOADER-ROLLBACK) |
| The generated witnesses are the model | `loaderSource_agrees`, `loader_witness_agrees_load`, `loader_witness_agrees_start` |

The loader names a segment only by its index in the admitted plan and claims
only its source. It cannot choose an address, a size or a permission. A claimed
source outside the read authority, or one that is not the segment's admitted
placement, is rejected. Every rejection of a request for the live child rolls
the spawn back. The kernel terminates the child through the generated
dispatcher's edge (`childGate (.terminateChild _)`, the spawn table's
`granted` to `terminated`), which releases everything spawn and the grant
gave it (`terminateChild_releases_everything`), and discards the child's
pages.

The spawn table gains three states for the loaded child. The first child's
termination is followed by a spawn into the same child-table slot
(`loaderRespawned`), a frame grant (`loaderGranted`), and the child's
termination (`loaderTerminated`).

### What is not proved

- **The child's run is not a composite step.** The composite model's
  scheduler admits no spawned child (ADR 0010, "What the model does not yet
  give the child"). Starting the child is a transition of `ChildLoader` only.
  The child's one send is checked by the kernel against the child's slot-0
  send-only endpoint and is not a composite IPC step.
- **The contents of the copy are not modeled.** The model records which
  pages are copies. It does not record their bytes. The QEMU run checks the
  contents: the child's word includes an initialized data word and a bss word.
- **The kernel's half is trusted.** This covers its read of the program
  headers, its page-table writes and byte copy, and the child switch in
  `boot.S`. The composite model's frame stays free and scrubbed across the
  copy, so the kernel scrubs the frame before the child's termination returns
  it.

## Amendment (2026-10-16): the loader and the composite model together (#571)

The 2026-10-11 amendment left three gaps: the rollback pairing, the child's
send, and the copied bytes. Issue #571 closes them in the model. The kernel's
C half is unchanged, and so is the `spawn-loader` transcript.

### Joint rollback

`LeanOS.ChildLoaderJoint` puts the composite state and the loader state in one
state. A loader request that rolls back is paired with
`childGate (.terminateChild control)` for the control word the request names,
as the kernel's `loader_rollback` pairs them. `joint_rollback_restores`
(SC-LOADER-JOINT-ROLLBACK) covers the following run:

1. From a composite state that satisfies the invariants, with a loader that
   holds no child, spawn a child through the gate.
2. Grant it frames any number of times.
3. Run any loader requests, until one rolls back.

After that request, the loader is exactly the loader before the spawn. The
composite state is `SpawnRestored` against the state before the spawn: the
same live subjects and capability slots, the same runnable set and current
subject, the same ownership records, frame commitments, allocator, bindings
and frame contents, and the same child tables and spawn authority. The
child's spawn records are cleared. This is `spawn_rejected_unchanged` for the
pair. It cannot be equality, because identities are never reused: the
child's identity stays issued, and the control generation has advanced.

### The child's send is a composite step

`FailStop.childSend` is the started child's syscall 8. It is the composite
endpoint send for a spawned child through its slot-0 capability, published as
the composite gate publishes a send. It keeps every invariant of the
whole-trace theorem (`childSend_preserves`). `ChildTraceStep.childSend` makes
it a step of `child_resource_trace`. An accepted send writes only the mailbox
of the endpoint the child's slot-0 capability names (`childSend_confined`).
After a spawn and grants, the started child is the spawned child, and that
capability is the parent's endpoint with exactly the requested rights
(`joint_child_send_confined`, SC-LOADER-CHILD-SEND).

### Copied contents

`ChildLoader.State` now records the admitted file's bytes in the reserved
range (`file`) and the bytes of the child's frames (`frameBytes`). A copy
writes each byte of the claimed source while it is below the segment's file
size, then zeros (`copyByte`). Rollback scrubs the frames. `Contents` says
every page holds its segment's bytes, and every request keeps it
(`step_preserves_contents`). After `start`, every address of a writable
segment's page-rounded image reads the admitted file byte below `filesz` and
zero past it (`started_writable_bytes`, SC-LOADER-CONTENTS). A read-only
segment reads its file bytes in place (`started_contents`).

### Evidence

The oracle corpus gains seven `loaderDecide` vectors along the scenario's
requests on the model's own states (`loader_trace_vectors_model`,
`loader_trace_replies`). Their decisions are the transcript's 517, 257, 1, 2
and 3, followed by two refusals after the start.

### Still not proved

- **The kernel's C half.** Its pairing of the two steps, its program-header
  read, its page-table writes and byte copy, and the child switch in `boot.S`
  are still trusted. The joint model says what that pairing must do. It is
  not a refinement of the kernel.
- **The child's scheduling.** `childSend` is the send alone. The kernel's
  entry to the child, and the parent's wake-up, are not composite steps.

## Amendment (2026-10-17): the rollback runs on the spawn allocator (#575)

The kernel no longer terminates a child whose load failed through the spawn
table's edge: the table is gone. It runs the spawn allocator's termination
command on the thirteen record words it holds
(`leanos_spawn_allocator_kernel`), which on every composite state the spawn
family runs on is the same `childGate (.terminateChild _)` step
(`SpawnAllocatorBoot.kernel_refines`). The pairing proved by #571
(`ChildLoaderJoint.joint_rollback_restores`) is unchanged.
