# ADR 0022: Device programs as capability-mediated kernel services

## Status

Accepted, issue #449. All three stages are implemented: stage 1 (model and
executor), stage 2 (canonical kernel service and the exact QEMU scenario,
`device-service`), and stage 3 (the Qotom capture, below).

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
  invocation continues after it (`wifi_start` in `hardware/wifi/wifi-exec.h`,
  `wifi_gen_resume` in `hardware/wifi/wifi-gen-exec.h`, `Sim.resume`). Budgets bound each invocation,
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
agreement with the model remains tested (ADR 0020), and on the J1900 DMA
through xHCI descriptors is confined by the policy's descriptor map, under an
assumption about the xHCI specification (ADR 0021). Moving to (b) would
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
   *Model half done:* `BlockingIPC.keyCycle_delivers` and `keyCycle_returns`
   prove, for any state satisfying `CycleReady` and any payload, that one
   exchange delivers exactly that payload and returns to the same state;
   `keyStream_delivers` (claim SC-IPC-EVENT-STREAM) lifts this to any
   sequence of payloads, and `bootInitial_cycleReady` shows the reviewed boot
   state qualifies.
   *Runtime half done:* the q35 `ipc-stream` scenario
   (`LEANOS_IPC_STREAM_SCENARIO`) runs the exchange in a loop. Subject A takes
   events from a source (a fixed string for now; the device service in the
   next step) and sends each one; `boot.S` copies A's two send registers into
   B's wakeup frame and resumes A after B blocks again; B echoes the words and
   the kernel requires them to equal what A sent. Each edge is checked
   against the generated export `leanos_blocking_ipc_event`
   (`blockingIpcEvent_agrees_demo`, `blockingIpcEvent_accepts_only_edges`,
   oracle-replayed on the host), and the serial transcript is exact.
2. **An echo target.** The early text console is disabled before quarantine
   and before any ring-3 entry, because quarantine may remove VGA decode.
   The echo subject of `device-service` has no output authority: it hands
   each key to syscall 9.
   *Resolved by issue #493:* the echo target is the console object of the
   console server (issue #472, [console-server.md](../console-server.md)).
   The `keyboard-echo` image runs this device service inside the
   console-server image. Subject 1 holds the device capability but no
   console capability. It sends each key to the console server, subject 3,
   which writes it through the console capability, so the echo reaches the
   wire only as `@10/CONSOLE@` records. Subject 3's own device invocation is
   refused. `LeanOS/KeyboardEcho.lean` proves the separation in the composed
   model (claim SC-DEVICE-CONSOLE-SEPARATION). The kernel checks its device
   capability table against the generated witness `leanos_device_authorize`
   (`KeyboardEcho.deviceAuthorize_agrees`) and each key exchange against
   `leanos_blocking_ipc_event`, with subject 3 in the model's receiver role.
   `device-service` stays the two-subject baseline of this stage, with the
   VT-d window and the DMA/VT-d gates. Its kernel no longer prints the key
   on subject 2's behalf: the delivery record carries no `echo=` field, and
   the key's value stays in the send record's `payload0=`.
3. **A q35 xHCI platform variant.** Done. `leanos_q35_device_service_command`
   appends `qemu-xhci` at 00:02.0, a hub and a `usb-kbd` to the unchanged
   production construction (topology `0001000800020004`, validated like the
   assigned-EDU variant). The kernel admits exactly that function, quarantines
   it, and after VT-d translation is enabled places BAR0 at the pinned
   `0xFEBF0000` (so firmware placement does not matter), maps its 16 KiB
   through the assigned-device window of the generated boot page-table plan,
   and enables memory decoding. The controller's only DMA authority is
   `VTdBootPlan.deviceServiceState`: one read/write grant of four model pages
   that the requester-16 tables `VTdBootPlan.compile` produces map at IOVA
   16 KiB onto the first four pages of the executor scratch
   (`deviceServiceState_shape`, `deviceServiceTransfer_window`,
   `accepted_translation_exact`); the `qemu` layout of `LeanOS.Usb.Xhci`
   keeps every DMA structure inside them. The program enables bus mastering
   only after resetting the controller: SeaBIOS leaves qemu-xhci running with
   rings in firmware memory, and the first run of the scenario showed VT-d
   refusing exactly that stale DMA.
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
5. **Entry-path rules.** The executor's `switch` compiles without jump
   tables in both toolchain lanes (the Clang lane's global `-fno-jump-tables`,
   a scoped GCC pragma around the executor). Its configuration and PM-timer
   hooks are pinned in the direct-port audit (source sites and final-ELF
   callers). The device-service image is under the same final-ELF
   entry-stack call-graph gate as the canonical image (#469):
   `scripts/entry-stack-device-service-callgraph.tsv` reviews every function
   reachable from the entry roots, the executor and its hooks included. The
   syscall path, which runs the executor for syscall 60, needs 6456 bytes of
   the 16 KiB guarded entry stack (margin 9928). The build also runs a
   negative check: a manifest without `wifi_hook_delay_us` must fail and name
   it. Any new edge, indirect call or larger frame fails the build.
6. **The scenario.** Done: `device-service` (`LEANOS_DEVICE_SERVICE_SCENARIO`
   on top of the `ipc-stream` exchange). Subject 1, the holder of the one
   assigned device, invokes the driver with syscall 60; the kernel binds the
   embedded `kbd-q35-service` image only if its declared target and policy lie
   inside `q35XhciPolicy`, then resumes it in bounded slices until it yields a
   key. Subject 1 sends each key over the verified blocking IPC to subject 2,
   which echoes it. `scripts/type-device-service.py` types `lean ipc⏎`
   through QMP once the program reports the keyboard ready, and
   `scripts/run-image.sh` compares the complete serial transcript exactly
   (`scripts/expectations/device-service.transcript`), including the VT-d
   assignment record.

Stage 3 repeats the path on the Qotom with a real keyboard. The lab builder's
`--ipc-device-stream` extends the audited `qotom-blocking-ipc-v1` profile:
after whole-platform admission the kernel binds the Bay Trail keyboard
program for subject 1. Each "next key" syscall maps the xHCI BAR through
borrowed leaves of the closed root and resumes the program in budgeted
slices. Subject 1 sends each key to subject 2, which echoes it, and every
edge is checked against `leanos_blocking_ipc_event`. The IPC audit pins the
extended syscall traces. The [2026-10-07 observation](../../hardware/lab/observations/qotom-device-stream-20261007/README.md)
captured 231 typed keys (`hello lean⏎` typed 21 times), all delivered and
echoed, ending in `FINAL status=PASS events=231`. On the J1900 the
controller's DMA is confined by the program's address sinks and
descriptor map alone (ADR 0021).

## Second device: AHCI read-only, one sector (issue #496)

The `ahci-service` image repeats the pattern for a second device, q35's
built-in ICH9 AHCI at 00:1f.2, with the Lean program
`LeanOS.Storage.AhciRead` ([storage-ahci.md](../storage-ahci.md)). It reads
one sector at a fixed LBA of a generated fixed disk behind port 1 and yields
its 128 dwords; subject 1 sends each over the same verified blocking IPC to
ring-3 subject 2, and the exact transcript
(`scripts/expectations/ahci-service.transcript`) carries every dword and the
sector's FNV-1a digest, which `scripts/generate-ahci-service-disk.py
--check-transcript` ties to the generator. What stayed the same: the
generated executor and its hooks, the budgeted resumable invocation on
syscall 60, binding only an image whose declared target and policy lie inside
the kernel's profile (`q35AhciPolicy`), the confinement and descriptor
theorems (now with an AHCI descriptor map, ADR 0021), a VT-d grant generated
from a Lean model state (`VTdBootPlan.ahciServiceState`: one read/write page
at IOVA 16 KiB over the scratch, requester 250), and the IPC exchange checked
edge by edge against `leanos_blocking_ipc_event`.

No new executor architecture was needed. What had to change, and why:

* **Assignment of a production function.** The xHCI is an extra function the
  device-service manifest admits as assigned from the start. The AHCI is
  part of the production inventory (it holds the boot CD), so the image keeps
  the production manifest and its generated snapshot check unchanged (the
  AHCI is quarantined unassigned at Command=0) and assigns it only after VT-d
  translation is enabled. The live CPL3 gates of every device-service image
  therefore read the *live* assignment bit instead of the manifest's; for
  the xHCI images the two are equal.
* **A second requester.** The xHCI shares EDU's requester 16, so its images
  install the assigned context table. `leanos-vtd-plan` now takes the
  service's reviewed assignment (`serviceOf`: 1 xHCI, 2 AHCI, selected by the
  image's `leanos_service_device` symbol), binds it to that service's
  requester, emits `leanos_vtd_service_context_table`, and refuses a service
  plan whose upper tables differ from the assigned ones. The AHCI image
  installs that context table.
* **Holder check.** The two-subject `device-service` image authorizes
  syscall 60 by subject and step only. The AHCI image also checks every
  invocation against the generated device witness `leanos_device_authorize`
  (`KeyboardEcho.deviceAuthorize`: only subject 1 holds device 0), and
  subject 2's one attempt is refused by the same witness before it first
  blocks.
* **Framing.** A key is never zero, but a sector dword may be, and zero ends
  the stream. The AHCI image returns each dword with its sequence number
  (from 1) in the high half of syscall 60's result; subject 1 sends them as
  the two payload words and the kernel checks the sequence at delivery.
* **Window granularity.** The handwritten image parser
  (`wifi_image_header`) accepted target windows only in 2 KiB units. The
  AHCI policy's window is the host control registers and ports 0 and 1
  (512 bytes), so that ports 2–5, whose command-list and FIS bases are not
  address sinks, are out of reach; the parser now accepts 512-byte units.
  The Lean side (`admissible`, `Sim`) never had the restriction.
* **Release and scrub.** The keyboard program's scratch is not scrubbed when
  it ends. When the AHCI program halts (with Bus Master already cleared) the
  kernel releases the function: it requires Command=Memory, writes
  Command=0, unassigns it for the live gates, zeroes the whole 256 KiB
  scratch and reads it back. The VT-d grant is a static generated plan and
  stays installed; revoking it needs a second plan.

The scratch is still the static `wifi_scratch` array, not frames charged to
the holder's budget (issue #449's item 2), for both devices.

## Consequences

* The executor gains `yield` and resumption; the differential fuzzer and its
  mutation set cover both.
* Stage 2 changes the kernel image, platform variants and page-table plans,
  each behind its own review.
