# Complete Qotom PCI inventory observations

These proofs bind one supplied observation to the complete retained AHCI inventory. They preserve every raw register for later quarantine checks; they do not establish complete hardware enumeration or DMA safety.

- `decodeAll_preserves_raw` — Decoding a list of PCI headers successfully retains every original raw header in the supplied order.
- `check_preserves_raw` — A successful complete inventory check returns exactly the raw headers supplied by its caller, including command and forwarding-window registers.
- `witness_has_complete_inventory` — Every inventory witness matches the entire closed baseline, rather than independently selecting device identities from different profiles.
- `witness_has_fifteen_functions` — Every inventory witness contains exactly fifteen functions.
