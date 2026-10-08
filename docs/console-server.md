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
is meant to install `bootAuthority`: only the server holds the console
capability, and only `a` reaches the server.

| Claim | Theorem | Statement |
| --- | --- | --- |
| SC-CONSOLE-INTEGRITY | `console_integrity` | A subject holding neither capability cannot change the console trace. Erasing its actions leaves the final state unchanged, so two scripts that differ only in its actions print the same bytes. |
| SC-CONSOLE-CONFIDENTIALITY | `console_confidentiality` | Such a subject observes exactly one refusal per action of its own, so its observations do not depend on console input. |

The negative fixture `tests/negative/ConsoleCapabilityToSecondSubject.lean`
gives `b` the console capability too. The integrity claim then no longer
applies to `b`, and `check.sh` requires that fixture to fail to typecheck.

## Exclusions

- **No refinement.** No console image boots yet, so nothing ties the model to
  generated C, `boot.S` or a ring-3 server.
- **No capability transfer.** Authority is static in this model.
- **No timing or covert channels.**
- **Not the diagnostic stream.** The kernel's `@N/...@` records are a separate
  kernel channel. The theorems cover the console object, not that stream.

## Remaining slices

1. **A third subject.** Generalize the image from two hardcoded subjects to a
   fixed N = 3, with every existing transcript unchanged.
2. **The console object.** Add the capability-checked `write` and `read`
   syscalls behind a new capability kind. The server is its only holder.
3. **The service.** The server loops on a blocking receive on its endpoint and
   writes each payload. An exact QEMU transcript shows two things: `a`'s word
   is printed, and `b`'s attempt is refused.
