# Publishing a revocation only after the flush is acknowledged

Deciding to revoke a translation and actually flushing it from the hardware cache are two different moments, and the gap between them is exploitable. This file models a strict receipt protocol: every accepted change is held pending under a fresh ticket together with the exact flush the machine must perform, only an acknowledgement quoting both the ticket and the exact flush publishes the change, and retired memory cannot be handed out again until both the release and the destruction have been acknowledged.

- `initial_wellFormed` — The protocol's starting state already satisfies the cache-size invariant, with nothing pending.
- `prepare_retains_published` — Preparing a change never alters what the rest of the system can see; the visible state stays exactly the pre-state.
- `prepare_preserves_wellFormed` — Preparation can never publish a cache that breaks the size bound, and whenever it accepts, the successor it records behind the ticket satisfies the same bound.
- `prepare_rejected_inert` — A rejected preparation changes nothing and asks the machine to do nothing.
- `prepare_wrong_kind_inert` — A caller cannot relabel a mapping change as a lifecycle retirement or vice versa; a mismatched label is refused, changes nothing, and asks for no machine work.
- `acknowledge_rejected_inert` — A rejected acknowledgement changes nothing and asks for nothing.
- `acknowledge_accepted_exact` — An accepted acknowledgement is possible only when a change was pending and the receipt quoted both its exact ticket and its exact flush, and it then publishes exactly that pending successor and clears the pending slot.
- `acknowledge_preserves_wellFormed` — Acknowledgement either does nothing or publishes the exact recorded successor, so the cache-size bound survives without ever trusting the receipt's contents.
- `prepare_accepted_fresh_ticket` — Every accepted preparation takes its ticket from the current counter and advances that counter before any acknowledgement can possibly arrive.
- `prepare_accepted_pending_exact` — An accepted preparation records the exact computed change behind its fresh ticket, so neither the operation's kind nor its checked request can be swapped between the decision and its publication.
- `acknowledge_wrong_ticket_inert` — A receipt carrying any ticket other than the pending one is refused outright, even when its flush happens to look identical; an old completion can never be spliced into a later change.
- `release_not_published_before_ack` — A prepared release exposes nothing: the visible state remains literally the pre-state until the required flush is acknowledged.
- `reuse_publication_requires_retirement_ack` — Handing retired memory to a fresh object can happen only when nothing is pending and both the release flush and the destruction flush have been acknowledged.
- `publishReuse_preserves_wellFormed` — Publishing the reuse changes only the object-lifetime records; the already-flushed cache and its size bound stay exactly as they were.
- `canonical_effects` — A worked end-to-end sequence behaves as intended at every stage: wrong-owner and mislabeled requests are refused with no effect, each accepted stage names its exact flush, mismatched receipts are refused, and only the final fully acknowledged state permits reuse.
- `canonical_unmap_pending_retains_published` — In that worked sequence, preparing the unmap does not expose its successor; the visible state is unchanged until the page flush is acknowledged.
- `canonical_unmap_publication_order` — The exact acknowledgement of the unmap removes both the authoritative mapping and the cached translation for the affected page in one published step.
- `canonical_switch_away_back_publication_order` — Switching to another address space and back publishes neither switch until its own fresh ticket is acknowledged, and the first switch's receipt cannot authorize the second.
- `canonical_release_ack_cannot_splice_switch` — Although the release and the later address-space switch both require a full flush, the release's old receipt is refused for the switch and changes nothing.
- `canonical_retirement_and_reuse_order` — The full worked sequence lands exactly as intended: the permission downgrade takes effect, release unbinds the frame, destruction removes the owner, both retirements are recorded, and the reused frame belongs to a fresh object while the old page stays unmapped and unreachable.
