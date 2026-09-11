# Bounded PCI header observations

The decoder retains a conventional PCI header and exposes endpoint or bridge registers. These are observations supplied by a caller; the proofs do not establish complete enumeration, an atomic hardware snapshot, safe forwarding, or DMA containment.

- `decode_preserves_raw` — Successful decoding retains the exact bus/device/function address and all supplied raw words.
- `decode_transport_bounds` — Every accepted input has a valid bus/device/function address, exactly sixteen words, and no word larger than an unsigned 32-bit value.
- `observationWords_width` — Both endpoint and bridge observations produce exactly twenty scalar output words.
- `observe_success_tag` — A successful decode reports the success tag when the caller requests output field zero.
- `Scalar.status_eq_decode` — For every sixteen-word scalar input, validation returns exactly the reference decoder status, including BDF, dword, absent-function and layout errors. The separately checked retained object has no Lean runtime dependencies; enumeration and DMA policy remain outside this result.
