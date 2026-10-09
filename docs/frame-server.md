# Frame server

Issue #486 moves frame-allocation policy out of the kernel into a ring-3
frame server. The server decides who gets which frame. The kernel keeps the
mechanism (who holds which frame, scrubbing, mapping) and only checks the
server's decisions.

In the `frame-budget` scenario ([frame-budgets.md](frame-budgets.md)) the
kernel allocates through syscalls 20–25. This page describes the server-based
path that replaces that for the `frame-server` image.

## The model

`LeanOS/FrameServer.lean` is a finite, sequential model.

- **The pool capability.** The server subject (`System.server`) holds one
  capability over the frames in `pool`. It carries the mapping rights
  `poolRights`: bit 0 read, bit 1 write. No step changes the server, the pool
  or the pool rights.
- **Budget capabilities.** Each client holds a budget capability to the
  server: `limit client`, the number of pool frames it may hold at once. Only
  `revoke` changes a limit, and only to zero.
- **The kernel's record.** `grant frame` says which client holds a pool
  frame, and with which rights. A client's `usage` is the number of pool
  frames it holds. `bytes` are the frames' contents
  (`FrameScrub.FrameBytes`).
- **Decisions.** On a client's request the server makes one `Decision`. It
  chooses the client, the frame, the rights and the reason:
  - `grant client frame rights`;
  - `refuse client reason`, where the reason is `budgetExhausted` or
    `poolExhausted`;
  - `reclaim client frame`;
  - `revoke client`.
- **The check.** `check` accepts a decision only if all of these hold:
  - it comes from the server;
  - a granted frame is in the pool and free, and the client is below its
    limit;
  - the rights are a nonempty subset of the pool rights;
  - a refusal's reason is true;
  - a reclaimed frame is held by that client.
- **The effect.** `effect` does exactly what the decision names; the kernel
  chooses nothing.
  - A grant scrubs the whole frame with `FrameScrub.scrubFrame` before it
    records the grant.
  - Reclaim and revoke retire grants and leave the bytes in place, like
    `FrameScrub.release`.
- **Clients.** A client reads or writes only a frame it holds, and only
  within the rights of its grant.

`serverPolicy` is the honest policy. It grants the first free pool frame with
the pool rights while the client is below its limit. Otherwise it refuses with
the true reason.

| Theorem | Statement |
| --- | --- |
| `kernel_only_checks` | Every decision is either refused with the state unchanged, or applied as exactly `effect` |
| `decide_not_server` | A decision from any subject but the server is refused (`notServer`) |
| `granted_exact` | An accepted grant came from the server. It names a free pool frame, rights inside the pool rights, and a client below its limit. It installs exactly that grant over a completely scrubbed frame, and changes no other grant |
| `refused_truthful` | A refusal transfers nothing, and its typed reason is true |
| `serverPolicy_accepted` | The check never overrides the honest policy |
| `step_preserves_invariant` | `Invariant` is preserved by every server decision and every client write. It covers: no duplicate pool frames, every grant inside the pool with rights inside the pool rights, every client within its limit, and every unwritten held frame zero |
| `budget_respected` | No client ever holds more pool frames than its budget allows |
| `no_amplification` | No step changes the server, the pool or the pool rights, or raises a budget. Every grant stays confined to the pool |
| `grant_publishes_scrubbed` | After a grant, the new holder reads zero at every offset, whatever the frame held before |
| `release_preserves_bytes` | Reclaim and revoke do not scrub. Scrubbing happens at the next grant |
| `revoke_retires` | After a revocation the client holds nothing, and its budget is zero |
| `read_unwritten_zero` | In every invariant state, a held frame its holder has not written reads zero. A released or revoked frame is scrubbed before any client can see it again |

`LeanOS.SecurityClaims` restates these results as three claims:

- SC-FRAME-SERVER-BUDGET (`frame_server_budget`);
- SC-FRAME-SERVER-SCRUB (`frame_server_scrub`);
- SC-FRAME-SERVER-CHECK (`frame_server_kernel_checks`).

See [security-claims.md](security-claims.md) for the rows and their
exclusions.

The negative fixture `tests/negative/FrameServerReleaseScrubs.lean` tries to
derive the weakened claim that reclaim itself zeroes a frame, so that
publication could skip the scrub. `check.sh` requires it to fail to typecheck.

### The boot witness

`frameServerCheck op view usage limit requested held` is the allocation-free
export `leanos_frame_server_check`. Its inputs are the kernel's own words for
a decision:

- `op` is `opWord`: 1 grant, 2 refuse over budget, 3 refuse because the pool
  is exhausted, 4 reclaim, 5 revoke.
- `view` describes the named frame: 0 outside the pool, 1 free, 2 held by the
  client, 3 held by another client. For a pool-exhausted refusal it is 1 if
  some pool frame is free.
- `usage` and `limit` are the client's.
- `requested` is the granted rights, and `held` is the pool rights.

The answer is the encoded reply:

| Answer | Meaning |
| --- | --- |
| 1 | granted |
| 0x100 | the client's typed `budgetExhausted` |
| 0x200 | the client's typed `poolExhausted` |
| 3 | reclaimed |
| 5 | revoked |
| `0xf00 + reason` | the kernel refuses the decision: 2 outside the pool, 3 frame in use, 4 rights, 5 over budget, 6 not the holder, 7 untruthful refusal, 8 unknown op |

`frameServerCheck_agrees` proves that, for every system and every decision of
the server, the witness over those words equals the model's encoded reply.
The model oracle replays it as adapter `FrameServer.check` (id 26) over 16
vectors, `hosted_frame_server_vectors_exact`.

The view itself also comes from generated code:
`frameServerView op index poolSize holder client free` is the export
`leanos_frame_server_view`. Its inputs are the kernel's raw words: the
frame's holder (0 when free) and the number of free frames.

- `frameServerView_agrees` proves that, for a grant or a reclaim, it equals
  `frameView` for a pool of the frames `0 .. n - 1`.
- `frameServerView_pool` proves the same for the pool-exhausted bit.

The oracle replays it as adapter `FrameServer.view` (id 27) over 8 vectors,
`hosted_frame_server_view_vectors_exact`.

## The frame-server image

The `frame-server` scenario is the `three-subject` image with three
differences:

- **C, the frame server**, is built from `subjects/frame-server` with the
  subject template ([subjects.md](subjects.md)).
- **A, client 1**, has a budget of one frame.
- **B, client 2**, has a budget of two frames.

Everything is behind `LEANOS_FRAME_SERVER_SCENARIO`. No other image changes.

### The pool and the mechanism

- **The pool.** It is two page-aligned frames reserved in the kernel image.
  At boot they hold the residue 0xff, standing for whatever a frame held
  before.
- **The kernel's tables.** The kernel keeps the holder and rights of each pool
  frame and each client's limit. This is the mechanism; the kernel holds no
  policy.
- **A grant.** The kernel zeroes all 4096 bytes and checks them. Only then
  does it set the client's leaf for that page to a user, writable, no-execute
  identity leaf, followed by `invlpg`.
- **A revocation.** The kernel restores the leaf it replaced and invalidates
  it. It leaves the bytes.

Before any subject runs, the kernel checks three things:

- every pool leaf is supervisor-only in all three roots;
- the frames hold the residue;
- the witness refuses eight hostile decision words (the words of
  `boot_hostile_refused`).

### Syscalls

| Number | Subject | Operation |
| --- | --- | --- |
| 7 | C | first receive on endpoint 12 |
| 62 | B | the three-subject run from B's initial context |
| 90 | A, B | request on endpoint 12. RBX 1 asks for a frame; the answer is the frame's page address or the typed 0x100. RBX 2 releases the client's budget (A only), and the client never runs again |
| 91 | C | the decision for the pending request: RBX op \| rights << 8, RCX client, RDX pool frame. C then blocks on endpoint 12. It is woken with the next request in RAX and the kernel-attested client in RBX |
| 93 | B | report the first and last byte of the frame and its address (final) |

### The run

1. The kernel checks C's slot and roots, installs the pool and the budgets,
   and checks the witness. C blocks on endpoint 12.
2. B runs once from its initial context and reports its canaries. A is
   dispatched fresh.
3. A asks for a frame. C's policy grants pool frame 0 with read and write.
   The witness gives `granted`. The kernel scrubs the frame, maps it into A's
   root, and A resumes with its address. A writes 0xa5 to the first and last
   byte and reads both back in CPL3.
4. A asks again. A is at its limit (one frame), so C refuses with
   `budgetExhausted`, although frame 1 is still free. The witness agrees
   (0x100), nothing is transferred, and A resumes with 0x100.
5. A releases its budget. C revokes A's budget capability, and the witness
   gives `revoked`. The kernel unmaps frame 0 from A and sets A's limit to
   zero. It then reads the frame back: both bytes are still 0xa5 (release
   does not scrub). A never runs again.
6. B resumes and asks for a frame. B is below its limit (two), so C grants
   the first free frame, which is frame 0 again. The kernel scrubs it before
   mapping it into B's root.
7. B reads the first and last byte in CPL3 (both zero) and reports them with
   the address. The kernel checks the counts: two grants, one refusal, one
   revocation, frame 0 held by B, A's budget zero. It then prints
   `@10/FINAL@ status=PASS`.

`scripts/expectations/frame-server.transcript` is the exact transcript. The
same run in the model is `bootSystem` through `grantedB`:

- `boot_grant_a`
- `boot_written_a`
- `boot_refuse_a`
- `boot_revoke_a`
- `boot_grant_b`

```sh
python3 scripts/run-emulator-evidence.py run --scenario frame-server --output frame-server.json
```

## Exclusions

- **No refinement.** The QEMU run is one finite trace. The witness check
  covers the decision only. The kernel's scrub loop, its leaf writes and
  `invlpg`, and the raw words it hands the two witnesses (holder, usage,
  limit, free count) are hand-written C, and are tested, not proved. `boot.S`, the subject build
  rule and the ring-3 server are not proved to implement the model.
- **A fixed pool and fixed budgets.** There is no dynamic pool, no second
  server, and no budget transfer or minting after boot. The pool frames are
  reserved in the kernel image. They are not allocator-enumerated frames, and
  they are not tied to `FrameBudget`'s admission partition.
- **No sharing, paging or swap.** A frame has at most one holder. The issue
  excludes paging policy, swapping and shared memory.
- **No liveness.** The server may refuse anything with a true reason, and the
  model does not schedule it.
- **No timing claims.** Covert channels, caches and DMA are not modeled.
- **The schedule** is the kernel's fixed state machine, as in the other
  three-subject images.
