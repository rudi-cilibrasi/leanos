# Console server

Issue #472 makes a ring-3 console server the first Phase 3 service. This page
records the design choice for the console capability and what is proved so far.

## Design choice: a kernel console object

Issue #472 offers two designs:

- **(a) Kernel console object.** The kernel keeps the UART. It exposes a console
  object whose `write` and `read` are capability-checked syscalls, and the
  server is the object's only holder.
- **(b) Ring-3 port I/O.** The server is granted the COM1 port range through the
  direct-port audit and the I/O permission bitmap.

LeanOS uses **(a)**, for three reasons:

- **Port I/O stays in the kernel.** Every port access is already pinned by
  `scripts/direct-port-sites*.tsv` and the direct-port audit. Design (b) would
  add the first ring-3 port grant, with its I/O-bitmap and TSS checks. That is
  a separate trust change that should not be bundled with the first service.
- **The theorem is about capabilities, not ports.** Under (a), "may emit a
  console byte" is the same as "holds the console capability". The same
  `Capability` checks that every other kernel object uses decide it.
- **(a) is smaller.** It needs one object and two syscalls. The boot image
  already writes COM1 from the kernel.

Design (b) remains the shape for real drivers. The device-program work (ADR
0020 to 0022) is where ring-3 hardware access is being built.

## What is proved

`LeanOS/ConsoleServer.lean` models three fixed subjects:

- `a`, the client;
- `b`, a subject with no console authority;
- `server`, the console server.

Authority is a static assignment. It says who holds the console capability and
who holds a send-only endpoint capability that reaches the server. The image
installs `bootAuthority`: only the server holds the console
capability, and only `a` reaches the server.

| Claim | Theorem | Statement |
| --- | --- | --- |
| SC-CONSOLE-INTEGRITY | `console_integrity` | A subject holding neither capability cannot change the console trace. Erasing its actions leaves the final state unchanged, so two scripts that differ only in its actions print the same bytes. |
| SC-CONSOLE-CONFIDENTIALITY | `console_confidentiality` | Such a subject observes exactly one refusal per action of its own, so its observations do not depend on console input. |

The negative fixture `tests/negative/ConsoleCapabilityToSecondSubject.lean`
gives `b` the console capability too. The integrity claim then no longer
applies to `b`, and `check.sh` requires that fixture to fail to typecheck.

## The console-server image

The `console-server` scenario boots the three subjects of the `three-subject`
image (slice 1, `LEANOS_THREE_SUBJECT_SCENARIO`) with the console object and
the server (`LEANOS_CONSOLE_SERVER_SCENARIO`). Every other image, including
`three-subject`, is unchanged.

### The console capability

The kernel keeps a read-only capability table indexed by subject and slot. A
slot holds a kind (empty, endpoint or console), rights, and an object:

| Subject | Slot 0 | Slot 1 |
| --- | --- | --- |
| A (1), client | endpoint 12, send only | empty |
| B (2) | empty | empty |
| C (3), server | console, write and read | endpoint 12, receive only |

The syscalls name a slot of the caller's own table in RDX:

| Number | Operation | Arguments | Result |
| --- | --- | --- | --- |
| 70 | console write | RBX byte | 0 accepted |
| 71 | console read | none | 256 when no byte is ready (see below) |
| 8 | send | RBX word, RCX second word | 0 when the sender resumes |
| 7 | receive (blocks) | none | RAX word, RBX second word, RCX 1 |

A refused request changes nothing and returns `1 | reason << 8`. The reasons
are typed: `bad-slot` (1), `empty-slot` (2), `wrong-kind` (3),
`missing-right` (4), `bad-byte` (5) and `input-not-admitted` (6). The kernel records each refusal as a
`@10/CAP@ event=refuse` diagnostic with the subject, operation, slot and
reason.

Each decision is made from the table and then checked against
`leanos_console_authorize`, the generated export of
`ConsoleServer.consoleAuthorize`. `consoleAuthorize_agrees` proves that the
export equals `permitted bootAuthority` for every subject and operation. A
request that the table accepts and the model refuses stops the kernel
(`console-model-decision`). The table may refuse more than the model: a wrong
slot, or a byte that is not printable. Before any subject runs, the kernel
also checks that the table names one console holder (C) and one sender (A),
and that for every subject and operation it grants exactly what the witness
accepts (`@10/CAP@ event=install ... model=agree`).

The read polls the COM1 line status, which is reviewed serial input
(port `0x3fd`). Consuming a byte would read the receive register (input from
port `0x3f8`). `DirectPortIO.portManifest` does not admit that read, and the
direct-port audit pins every byte-wrapper call. So a ready byte is refused
with `input-not-admitted` instead of being read.

### The console object's output

The console object is line-buffered. Each line is emitted as one
`@10/CONSOLE@` record, and `console_object_flush` is the only emitter of that
record (`check-image-policy.sh` requires it). The object accepts only
printable bytes and newline. So a reader that anchors on line starts can tell
the object's stream from the kernel's own diagnostic records on the same
COM1 wire. The other `@N/...@` records are the kernel diagnostic channel.
They are not console-object output and are not covered by the theorems.

### The run

1. The kernel checks C's page tables and the capability table, then enters C.
2. C reads the console. The QEMU serial line has no input, so the read
   returns 256.
3. C blocks on a receive through slot 1.
4. B is dispatched from its initial context. It tries a console write, a send
   and a console read through slot 0. Each is refused with `empty-slot`, and
   the model refuses each too. B then reports its canaries and the three
   result words it observed. The kernel requires exactly three refusals.
5. A is dispatched. Its console write through slot 0 is refused with
   `wrong-kind`, because slot 0 is an endpoint capability.
6. A sends `hello` (five bytes, least significant first) through slot 0. C is
   woken with exactly A's words. It writes the five bytes and a newline, and
   the kernel prints `@10/CONSOLE@ hello`.
7. C blocks again, and A resumes with result 0. A then sends `world` the same
   way.
8. A finishes. The kernel checks the counts (2 deliveries, 2 console lines,
   12 bytes, 4 refusals, 3 blocks) and prints `@10/FINAL@ status=PASS`.

`scripts/expectations/console-server.transcript` is the exact expected
transcript. `ConsoleServer.bootScript` is the same run as a model script.
Its theorems give the console trace `hello\nworld\n` (`boot_output`), B's
three refusals (`boot_b_refused`) and A's observations
(`boot_a_observations`).

To support the run, the model gained a `receive` operation: the server
receives a word without writing it. It is gated by the console capability,
like `serve`.

## Exclusions

- **No refinement.** The QEMU run is one finite trace. The witness check
  catches only an accepted decision that the model refuses. Nothing proves
  that the C, `boot.S` or the ring-3 server code implement the model.
- **No capability transfer.** Authority is static in the model, and the
  kernel table is read-only.
- **No console input in the run.** The serial line is a file with no input,
  so the confidentiality half is exercised only for refusals.
- **No timing or covert channels.**
- **Not the diagnostic stream.** The kernel's `@N/...@` records, apart from
  `@10/CONSOLE@`, are a separate kernel channel. The theorems cover the
  console object, not that stream.

## Remaining work

- **Replies.** Once the reply capability exists (#471), the server replies
  to A with a status word instead of A's send returning when C next blocks.
- **Scheduling.** The three-subject schedule is the kernel's own fixed state
  machine. It is not yet bound to the capacity-parameterised `Scheduler` and
  `BlockingIPC` models.
- **Console input.** Admitting the COM1 receive register in
  `DirectPortIO.portManifest` and the direct-port audit would let the read
  return input bytes, as the model's `read` does.
- **A generic capability table.** The console table is specific to this
  scenario. Moving it into the kernel's general capability space comes with
  the subject template.
