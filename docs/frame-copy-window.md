# Frame copy windows

Issue #569 asks for a production Qotom image in which the WiFi driver, the
DHCP client and the echo responder run as three ring-3 subjects, each in its
own address space. Frames cross between them through the kernel. On q35 the
kernel copies a frame through the SMAP user-copy window
([network-subject.md](network-subject.md)). The Qotom's J1900 has no SMAP,
so the lab image used the audited bounded copy roots instead
([ADR 0017](adr/0017-qotom-kernel-copy-roots.md)). They have two limits:

- they alias only subject A's two stack pages, so the DHCP subject and the
  echo subject had to take turns in subject A;
- they move sixteen bytes per transfer, so a 98-byte ping took seven root
  switches each way, and a ping took about 125 ms.

A **copy window** replaces the copy roots for frame transport. It needs no
SMAP, it serves every port holder in its own address space, and it moves a
whole frame in one transfer.

## Design

Each port holder has a *window*: one or two whole pages of its own memory,
which hold its frame buffer. Before any subject runs, the kernel builds two
*window roots* for each holder. It builds them from one source root with the
reviewed builder (`include/qotom_copy_root_builder.h`):

- the **closed root** is the source with every leaf of every user frame
  removed: no text, stack or window page of any subject;
- the **fetch root** is the closed root plus writable supervisor no-execute
  aliases of the holder's window frames, at reserved *alias slots*;
- the **send root** has the same aliases read-only.

The kernel checks each root leaf by leaf (`frame_window_root_exact` in
`include/frame_copy_window.h`). Outside the alias slots, each root equals
the closed root. The closed root maps no user frame. Each alias slot maps
exactly its window frame, with the expected permissions.

A copy request (syscall 64 fetch, 65 send) runs in this order:

1. The kernel decides it with the frame port witness
   `leanos_frame_port_check`, as before.
2. It asks the generated operand `leanos_frame_window_operand` for the alias
   address of the caller's buffer. The operand is nonzero exactly when the
   witness accepts and the window has the reviewed geometry. The kernel
   requires that agreement.
3. `frame_window_transfer` (`boot/boot.S`) disables interrupts and
   selects the caller's fetch or send root. It moves the frame with one
   `rep movsb` between the kernel's endpoint slot and the alias, then
   reselects the root it came from. It reads CR3 back after each load. It
   requires CR4.PGE and CR4.PCIDE clear, so each load flushes every
   translation. It also requires both roots to be page aligned and below
   16 MiB, and the length to be at most 1514. Any failure halts.

While the window is open, no other subject's frame is mapped. The alias
grants no user access and no execution. The send root cannot store.

## The model

`LeanOS/FrameCopyWindow.lean` models a root over 4 KiB leaves, the window
roots, and the string move as byte stores or loads through the selected
root. It relates physical memory to the per-subject memory of the endpoint
models with `Rel`: every byte of a frame a subject owns is that subject's
memory at the same address, because both platforms identity-map the arena.

| Theorem | Statement |
| --- | --- |
| `windowRoot_protected`, `windowRoot_other_absent`, `windowRoot_no_user` | A window root maps a protected frame only at its alias slots, only as a supervisor no-execute alias of one of the holder's own window frames, writable only in the fetch root; it maps no frame of another subject |
| `translate_alias` | The alias of every window byte translates to that byte's own physical address |
| `storeAll_alias`, `loadAll_alias`, `storeAll_readonly` | Through the fetch root, the string move stores exactly the model's `writeBytes` at the buffer; through either root it loads exactly the model's `readBytes`; the send root cannot store |
| `fetch_refines`, `fetch_footprint`, `send_refines` | An accepted fetch through the fetch root performs exactly `DhcpSubject.step`'s fetch, keeps `Rel`, and changes no physical byte outside the requested range of the caller's window; an accepted send reads exactly the model's reply |
| `network_fetch_refines`, `network_send_refines` | The same for the one-port `NetworkSubject` endpoint |
| `frameWindowOperand_ne_zero_iff`, `frameWindowOperand_alias`, `frameWindowOperand_fetch`, `frameWindowOperand_send`, `frameWindowOperand_nonholder` | The generated operand is nonzero exactly when the port witness accepts over the reviewed geometry; it is then the alias of the requested buffer, and the move from it stores or loads exactly what the model's step does |

So the confinement of SC-DHCP-SUBJECT-SEPARATION and
SC-NETWORK-SUBJECT-CONFINEMENT describes the copies the window performs.
`SecurityClaims.frame_copy_window` restates the theorems as claim
SC-FRAME-COPY-WINDOW ([security-claims.md](security-claims.md)).

`scripts/check-frame-window-host.sh` is the hosted generated-boundary row
`frame-window`. It runs the generated operand on fixed requests for every
refusal reason and every geometry rule. It also runs it differentially, on
200000 requests near the boundaries, against a C restatement of the
documented semantics and against the port witness itself.

## The `frame-window` scenario

The q35 `frame-window` image is the `dhcp-subject` image with every frame
copy moved off the SMAP window onto the copy window:

- the source root is A's boot root;
- the protected inventory is every user page of A, B and C: seven frames;
- B's window is its stack page, and so is C's;
- the alias slot is the page of B's text, which A's root does not map.

The kernel builds the closed root and four window roots and checks every
leaf. It checks the generated operand against the port witness for every
subject and route, then prints one `NET event=window` record. Every fetch
and send record names the root it went through (`copy=fetch-root` or
`copy=send-root`). The final record counts the window copies, which must
equal the fetches and sends. The exact transcript is
`scripts/expectations/frame-window.transcript`.

```sh
LEANOS_BOOT_SCENARIO=frame-window ./scripts/run-image.sh
```

On q35 the copy returns to the caller's own root, which maps the caller's
user pages under SMAP. On the Qotom the kernel runs on the closed root, and
the copy returns there.

## Not covered

- The construction of the roots from the boot page tables is checked by
  the kernel's scans, not proved. The kernel names the protected inventory
  and the alias slot; nothing proves the inventory complete.
- The string move, the CR3 loads and their readback, and the TLB are
  trusted. Interrupts are disabled, but an NMI or a fault during the move is
  not modelled.
- One QEMU run exercises the scenario; it is not a refinement of the
  booted kernel.
- The Qotom production image that uses the copy window has not run on the
  hardware yet.
