# Ring-3 subjects from `subjects/`

A subject is a ring-3 program linked into the boot image. Subjects A and B are
still handwritten assembly in `boot/boot.S`. Issue #484 adds a way to write a
subject in freestanding C, build it on its own, check it, and link it into a
reserved slot. Today that slot is subject C. Together with the ring-3 ABI
note, [userspace-abi.md](userspace-abi.md) (#483), this page is enough to
start a new subject.

There is no loader, no dynamic subject, and no libc. A subject is linked into
the image at build time, like every other byte of it.

## The directory

| Path | What it is |
| --- | --- |
| `subjects/template/` | The template: copy it to start a subject |
| `subjects/example/` | The example subject booted by the `example-subject` image |
| `subjects/runtime/entry.S` | The entry stub linked first into every subject |
| `subjects/include/leanos/subject.h` | The only kernel interface: `int $0x80` wrappers |
| `subjects/subject.ld` | The one linker script, used with `ld -r` |
| `subjects/fixtures/` | Negative fixtures the build rule must reject |

## The slot layout

The boot page plan gives a subject slot two ranges, and maps each with one
leaf:

| Range | Mapping | Contents |
| --- | --- | --- |
| text page | user, read-only, executable | the entry stub, then all code (at most 4096 bytes) |
| stack page | user, writable, no-execute | the stack (2048 bytes), then read-only data, data and bss (at most 2048 bytes) |

The text page holds code only, so the build rule disassembles every
executable byte. Read-only data shares the no-execute stack page. The stack
sits at the bottom of its page, so an overflow runs into the read-only text
page and faults instead of corrupting data. A subject that does not fit fails
to link: `subjects/subject.ld` sets the stack page to exactly 4096 bytes, and
`ld` reports `cannot move location counter backwards`.

## Entry, syscalls and exit

The kernel enters the subject at its first text byte, `subjects/runtime/entry.S`,
at CPL3, with RSP at the top of its stack. The stub calls `subject_main`.

A subject enters the kernel only through `int $0x80`, with the number in RAX
and arguments in RBX, RCX and RDX. `<leanos/subject.h>` wraps it. Every syscall
number is scenario-scoped: an image accepts it only from the subject and at the
step its kernel script expects, and anything else stops the machine. See
[userspace-abi.md](userspace-abi.md) for the numbers each image accepts.

**There is no exit syscall.** A subject that is done blocks forever, with
`leanos_block_forever(endpoint)`: a receive on an endpoint that nobody sends to.
`subject_main` must not return. If it does, the stub executes `ud2` and the
kernel fail-stops.

## The build rule

`scripts/build-subject.sh --cc CC --slot c --output OBJ subjects/NAME` builds
one subject:

1. **Compile.** Every `*.c` and `*.S` in the directory, plus the entry stub, is
   compiled on its own and freestanding. The flags are `-ffreestanding
   -fno-builtin -mgeneral-regs-only -fno-stack-protector -fno-pic
   -fcf-protection=none -O2 -Werror`, with no unwind tables.
2. **Link.** `ld -r -T subjects/subject.ld` collects the result into
   `.subject.text` and `.subject.bss`. This chooses no address.
3. **Check.** `scripts/check-subject-policy.py object` checks the object against
   the subject assembly and ABI policy. It rejects:
   - privileged or system instructions: `cli`, `sti`, `hlt`, `rdmsr`, `wrmsr`,
     descriptor-table loads and stores, `invlpg`, `wbinvd`, `iretq`, `sysret`,
     `swapgs`, and others;
   - `stac` and `clac`;
   - port I/O;
   - control, debug or test register access;
   - segment-register loads and far transfers;
   - x87, MMX, SSE and AVX registers, because extended state is denied at CPL3;
   - any kernel entry other than `int $0x80`, such as `syscall`, `sysenter`,
     `int3` or `int $0x81`;
   - undecodable bytes;
   - undefined symbols, so no libc and no kernel symbol;
   - any allocated section other than the two;
   - a layout other than the slot layout above.
4. **Rename.** `objcopy` renames the sections to the slot's input sections,
   `.user.c.text` and `.user.c.bss`. It renames the stub and stack symbols to
   `user_c_entry`, `user_c_stack`, `user_c_stack_top` and the slot marker
   `user_c_template_text`. Every other symbol gets the `user_c_` prefix and
   becomes local, so nothing in a subject can collide with or bind to a
   kernel symbol.

`scripts/test-build-subject.sh` runs from `check.sh`. It builds the template
and the example, and requires every fixture in `subjects/fixtures/` to be
rejected for its reason. The fixtures cover `cli`, `wrmsr`, `stac`, port I/O,
`syscall`, `int $0x81`, CR3, SSE, a libc call and oversized data.

`scripts/generate-image-object-graph.py` turns each `build.subjects` entry in
`scripts/scenario-manifest.json` into a Make rule that calls the build rule.
An image names the subject in its `extra_objects`.

## The boot page plan stays the authority

The build rule never picks an address. `boot/linker.ld` places `.user.c.text`
and `.user.c.bss` at C's slot, after B's. The Lean plan is then generated from
the linked prelink ELF, through the same `compile` and emit path as every other
image. `build-image.sh` compares the prelink and final plans. The guest walks
C's whole live root against the emitted `leanos_boot_plan_c` before C first
enters CPL3. Addresses flow from the linked image into the plan and the subject
symbols, never back.

## Final-ELF checks

Subject code built this way gets the same final-ELF checks as the rest of the
image:

- `check-image-policy.sh` checks C's sections, ranges, tables and context, as
  in the `three-subject` image. When `user_c_template_text` is linked, it also
  re-runs `check-subject-policy.py elf` on the final `.user_c_text`. That run
  covers the bytes that actually boot, and checks that the entry, the marker
  and the stack match the slot bounds.
- `build-image.sh` plants a `cli` in a copy of the final `example-subject`
  ELF, and requires that check to reject it.
- The direct-port-site check scans every executable section of the final ELF,
  so a port instruction in a subject would be an unreviewed site.
- The entry-stack gate runs on the image with
  `scripts/entry-stack-example-subject-callgraph.tsv`. Subject code is never a
  kernel stack contributor.

## The example subject

`subjects/example/main.c` sends one word, `0x5355424a` ("SUBJ"), on
endpoint 12, and then blocks forever on endpoint 13. The `example-subject`
image is the `three-subject` image with three changes:

- C comes from this object instead of `boot.S`.
- The kernel holds C's word in a one-word queue.
- A is a receiver.

The run goes like this:

1. The kernel checks C's slot, and walks C's root.
2. C enters CPL3 and sends its word, which is queued.
3. C blocks forever on endpoint 13.
4. B runs once from its initial context.
5. A is dispatched fresh, receives the word on endpoint 12, and reports it.
6. The kernel checks the word and C's preserved continuation, then prints
   `FINAL status=PASS ... blocked-forever=3`.

The exact transcript is `scripts/expectations/example-subject.transcript`. The
scenario runs in the evidence tier, on the `boot` runner:

```sh
python3 scripts/run-emulator-evidence.py run --scenario example-subject --output example-subject.json
```

## Adding a subject

1. Copy `subjects/template/` to `subjects/NAME/`, and write `subject_main`.
   Use only plain C and `<leanos/subject.h>`.
2. Run `scripts/build-subject.sh --slot c --output /tmp/NAME.o subjects/NAME`
   until it passes.
3. Add `"subject-NAME": {"source": "subjects/NAME", "slot": "c"}` to
   `build.subjects` in `scripts/scenario-manifest.json`.
4. Give the subject an image:
   - a boot object that defines `LEANOS_THREE_SUBJECT_SCENARIO` and
     `LEANOS_SUBJECT_C_OBJECT`, so `boot.S` builds C's tables but not C's
     code;
   - a kernel object with the scenario's macro and plan header;
   - an `images` entry that lists `subject-NAME` in `extra_objects`;
   - the `packaged_images`, `plan_checks` and `scenarios` rows.

   `example-subject` is the pattern to copy.
5. Write the kernel's script for the scenario in `boot/kernel.c`: which
   syscall numbers it accepts from C, and at which step. Add the exact
   transcript, an entry-stack manifest pair, and the scenario to the gated
   list in `build-image.sh`. Add the new numbers to the ABI table
   (`scripts/syscall-numbers.tsv`).

## Limits

- Only slot C can be built this way. A and B are shared by every image and
  remain in `boot.S`.
- A slot is one text page and one stack page. The plan and `boot.S` give U/S
  to exactly those two leaves.
- The kernel side of every scenario is still a script in `kernel.c`. The
  template gives a subject a body, not a general syscall layer.
