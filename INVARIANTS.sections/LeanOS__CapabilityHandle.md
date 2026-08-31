# Token words: a slot number plus a never-reused generation stamp

When a program talks to the kernel it does not hand over a permission token directly; it passes a single 64-bit number — a word — built from a 16-bit slot number and a 48-bit generation stamp that is never reused. This file proves the word format is exact and unambiguous (each accepted word means exactly one slot-and-generation pair), that the kernel checks the whole word — including the generation stamp — before acting on any request, and that once a slot is cleared or refilled, every old word for it is dead forever.

- `slotRadix_value` — Bookkeeping: the slot field of a word holds 65,536 possible values.
- `slotReserved_value` — Bookkeeping: the highest slot value, 65,535, is reserved and never names a real slot.
- `generationReserved_value` — Bookkeeping: the highest generation value, 281,474,976,710,655, is reserved and never stamps a real token.
- `wordSpace` — Bookkeeping: the slot and generation fields together fill a 64-bit word exactly, with no bits left over or missing.
- `decode_encode` — Turning a valid handle into a word and reading it back returns exactly the handle you started with.
- `encode_decode` — Every word the reader accepts is the one and only canonical encoding of the handle it reads out, so the accepted words are exactly the properly encoded ones and nothing else.
- `encode_injective` — One accepted word can never stand for two different handles.
- `copyWord_accepted_resolves` — Whenever a delegation request made with a raw word is accepted, the kernel first fully resolved that word — slot, generation stamp, and object kind — to the exact source token being delegated.
- `copyWord_accepted_fresh_handle_encodable` — An accepted delegation always allocates its new token inside the encodable range, so the fresh token can always be named by a valid word.
- `copyWord_accepted_returns_fresh_word` — A successful delegation hands back exactly the canonical word for the freshly created token in the destination slot.
- `copyWord_accepted_returns_installed_word` — The word handed back names the token actually sitting in the destination slot afterward, not merely what the kernel planned to put there.
- `copyWord_resolution_rejected_unchanged` — A delegation request whose word is malformed or fails any check changes nothing at all.
- `revokeWords_accepted_resolves` — Whenever a direct revocation made with raw words is accepted, both words — the revoker's authority and the victim token — were first fully resolved.
- `revokeWords_authority_rejected_unchanged` — If the revoker's authority word is malformed or denied, the revocation changes nothing.
- `revokeWords_target_rejected_unchanged` — Even after the authority word checks out, a malformed or denied victim word still changes nothing.
- `revokeSubtreeWords_accepted_resolves` — Whenever a transitive (whole-family) revocation is accepted, both the authority word and the word naming the family's root were first fully resolved.
- `revokeSubtreeWords_authority_rejected_unchanged` — A malformed or denied authority word makes transitive revocation change nothing.
- `revokeSubtreeWords_target_rejected_unchanged` — After the authority resolves, a malformed or denied family-root word still changes nothing.
- `resolve_issued` — A handle freshly issued for the token currently sitting in a live, in-range slot resolves to exactly that token.
- `resolve_sound` — A stepping-stone fact used by later theorems: whenever resolution succeeds, the caller is a live program, the slot is in range and holds exactly the returned token, and the token's generation stamp, kind, and live object registration all match.
- `resolveCurrent_sound` — The same guarantee for full-word resolution: success means the word decoded to exactly the recorded handle and every one of those checks passed.
- `clear_denies_handle` — Clearing a slot permanently invalidates the old handle for it, which is rejected as stale from that point on.
- `replacement_denies_old_handle` — Refilling a numbered slot with a new token cannot make an old generation stamp name the replacement.
- `clearSubtree_denies_descendant_handle` — When revocation removes a token's whole family, the handle of any removed descendant no longer resolves.
- `install_other_subject_cannot_resolve` — Identical handle words stay scoped to their owner: installing a token in one program's slot changes nothing about what the same word means for any other program.
- `live_issued_handles_nonaliasing` — Because live identity stamps are globally unique, two simultaneously live issued handles that look the same must name the very same slot of the very same program.
