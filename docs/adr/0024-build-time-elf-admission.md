# ADR 0024: Build-time admission of one subject ELF

- Status: Accepted, issue #492 (build-time half)
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
