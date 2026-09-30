# ADR 0022: Device programs as capability-mediated kernel services

## Status

Accepted for stage 1 (model and executor), issue #449. Stage 2 (canonical
kernel service and QEMU scenario) and stage 3 (Qotom capture) are planned
below and not yet implemented.

## Context

The Lean device programs (`docs/device-program-confinement.md`) run in a
separate lab kernel, in ring 0, before any subject exists. Their effects are
confined to a checked policy (`LeanOS/DeviceProgramConfinement.lean`), but
nothing ties *who* may cause those effects to the kernel's capability model:
the most capable code in the repository holds authority that no capability
mediates.

Issue #449 offered two execution models:

* **(a)** the executor stays in ring 0 and runs only on behalf of a subject
  holding a device capability, with a step budget; or
* **(b)** a ring-3 driver subject whose MMIO window is mapped into its own
  address space.

## Decision

Adopt **(a)** now, keeping (b) as the long-term shape.

* It reuses what exists: the executor is small, runtime-free and already
  confined by policy (ADRs 0020, 0021); the canonical kernel has no mechanism
  for mapping device MMIO into a ring-3 address space, for delivering device
  interrupts to ring 3, or for DMA-safe user memory.
* A device capability names one admitted device. A holder may *bind* a
  program only if it declares the device's policy and passes `admissible`,
  then *invoke* it for a bounded number of steps. Programs are resumable: the
  new `yield` instruction (opcode 27) suspends the program and hands one
  value — for the keyboard, one key — to the invoking subject, and the next
  invocation continues after it (`wifi_start`/`wifi_resume` in
  `hardware/wifi/wifi-exec.h`, `Sim.resume`). Budgets bound each invocation,
  so the driver cannot hold the CPU indefinitely.
* The model (`LeanOS/DeviceCapability.lean`) layers device capabilities,
  bound programs and suspended machines over an unmodified
  `Capability.State`, so the existing capability theorems apply unchanged
  (`cap_step_caps`, `non_cap_step_caps`). It proves that only an invocation
  by a current holder changes a device (`device_state_changes_only_by_holder`),
  that no sequence of transitions lets a device leave its policy (`run_inv`,
  claim SC-DEVICE-CAPABILITY-CONFINEMENT), that revocation ends access, and
  that one device's driver never touches another device.

## TCB delta

(a) keeps the executor (about 400 lines of C) and its hooks in ring 0 on the
subject's behalf, instead of the lab kernel's pre-subject call. Relative to
the lab kernel this *adds* mediation: a subject without the capability cannot
cause device effects, and each invocation is budgeted. The executor's
agreement with the model remains tested (ADR 0020), and DMA through
descriptors remains assumed on the J1900 (ADR 0021). Moving to (b) would
remove the executor from ring 0 entirely, at the price of MMIO mapping,
interrupt forwarding and DMA-buffer management for ring 3.

## Stage 2 plan: the q35 keyboard → IPC → echo scenario

Surveying the canonical kernel found these prerequisites, each a separate
change:

1. **A real IPC path.** The runtime blocking IPC is a Lean export that
   accepts one fixed demonstration payload (`leanos_blocking_ipc_demo`): a
   scalar witness of one block → send/wake → dispatch → deliver trace, tied
   to the `BlockingIPC` transitions by agreement theorems; the C kernel keeps
   no model state. The smallest extension that carries key events is a
   *payload-generic, cyclic* witness: the accepted edges ignore the payload
   words, one theorem shows that for every `(word0, word1)` the model's send
   delivers exactly those words to the blocked receiver (building on
   `wake_reserves_exact_envelope`), and another that the state after
   delivery and the receiver's next receive is again the blocked state, so
   the trace repeats once per key. The kernel then copies the words through
   its mailbox, as it does for the demonstration payload.
2. **An echo target.** The early text console is disabled before quarantine
   and before any ring-3 entry, because quarantine may remove VGA decode.
   Either keep the aperture mapped and decoded for the scenario, or echo on
   the serial console and record that choice.
3. **A q35 xHCI platform variant.** The q35 command is pinned to four devices;
   add a validated variant with `qemu-xhci` and `usb-kbd` (as the
   assigned-EDU variant does), a pinned BAR, a multi-page MMIO window in the
   boot page-table plan, and a VT-d domain that lets the controller reach
   only the executor scratch.
4. **A q35 target for the keyboard program.** Done (stage 2a): the driver is
   generated per `Xhci.Layout` (Bay Trail or `qemu-xhci`), reads xECP from
   HCCPARAMS1, and `q35XhciPolicy` confines the QEMU variant. The q35 device
   lab (`scripts/run-q35-device-lab.py`) runs it in the lab kernel on QEMU
   with QMP-typed keys, in `scripts/check.sh`. Its `--service` mode runs the
   yield-per-key program through a lab device service that follows
   `DeviceCapability.step` (grant, bind by admission, budgeted invocations,
   denial of an ungranted subject, revocation), with ring-0 stand-ins for
   the subjects; what stage 2 still adds is real ring-3 subjects, the IPC
   path and the canonical kernel's admission of the controller.
5. **Entry-path rules.** The executor's `switch` must compile without jump
   tables (`-fno-jump-tables` in both toolchain lanes) and every function
   reachable from the syscall entry must be listed with its stack budget in
   `scripts/entry-stack-callgraph.tsv`.
6. **The scenario.** Subject B holds the device capability and invokes the
   driver; each yielded key goes over IPC to subject A, which echoes it. Keys
   are injected through QMP `input-send-event`; the serial transcript is
   compared exactly, as in the other scenarios.

Stage 3 repeats the path on the Qotom with a real keyboard, which needs a
person at the keyboard during the capture.

## Consequences

* The executor gains `yield` and resumption; the differential fuzzer and its
  mutation set cover both.
* Stage 2 changes the kernel image, platform variants and page-table plans,
  each behind its own review.
