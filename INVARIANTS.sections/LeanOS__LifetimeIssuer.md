# Identity numbers: issuing them once and encoding them exactly

The kernel names every program and every object with an identity number drawn from a counter that only counts up, and each number fits in exactly one 64-bit machine word, with the all-zeros and all-ones words held back as reserved markers. These theorems guarantee that the counter hands out each number at most once, that it refuses cleanly when the numbers run out instead of wrapping around to reuse old ones, and that translating numbers to machine words and back never garbles a number or confuses two of them.

- `identityReserved_value` — Bookkeeping: pins down the reserved terminal marker as the concrete all-ones 64-bit value, 18446744073709551615.
- `identityRadix_value` — Bookkeeping: pins down the total size of the 64-bit word space as 18446744073709551616.
- `decode_encode` — Turning a valid identity number into its machine word and then reading that word back yields exactly the original number.
- `encode_decode` — Any machine word the decoder accepts is exactly the one canonical encoding of the number it decodes to, so the accepted words are precisely those the encoder itself could have produced.
- `encode_injective` — Two different identity numbers can never share the same machine word.
- `issue_deterministic` — What the counter hands out depends on the counter alone, so no input from any caller can change the result.
- `issued_facts` — Every successful issuance hands out exactly the counter's current value, moves the counter forward by exactly one, and stays inside the valid range.
- `issued_representable` — Every number the counter successfully hands out is a valid identity and can be written as a single machine word.
- `issued_bounded` — After any successful issuance the counter still sits at or below the reserved terminal marker; it never escapes the bounded range.
- `issued_strictly_monotone` — Every successful issuance strictly increases the counter, so no number can ever be repeated or revisited.
- `exhausted_issue` — A counter that has run out always refuses to issue; there is no wrap-around alternative.
- `issue_total` — Whether the counter issues or refuses is decided exactly by whether it has run out, so a successful issuance is itself proof that the counter was strictly within range.
- `exhausted_absorbing` — A counter that has run out can never produce a successor counter, so once exhausted it can never move again.
