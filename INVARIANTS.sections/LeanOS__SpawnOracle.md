# Spawn command encoding and adversarial test vectors

This section fixes one exact word encoding for a spawn request and checks the spawn step against a list of hostile and failure-inducing requests on a realistic kernel state. It is the general test boundary inside the Lean model; user programs cannot spawn, and the boot image's dispatcher reaches the same encoding only at the spawn family's own states.

- `decodeRights_encodeRights` — Every set of rights survives encoding into a word and decoding back.
- `rightsWords_canonical` — Every in-range rights word decodes to rights that encode back to the same word.
- `encodeRights_decodeRights_all` — Bookkeeping: the same fact for each of the 64 in-range rights words.
- `encodeRights_decodeRights` — A rights word that decodes is exactly the encoding of what it decodes to.
- `decodeSpawn_encodeSpawn` — Every spawn request with a nonzero spawn-permission word survives encoding and decoding unchanged.
- `encodeSpawn_decodeSpawn` — A spawn command that decodes is exactly the encoding of the request it decodes to, so no request has two encodings.
- `boot_dispatcher_rejects_spawn_tag` — The command decoder of the dispatcher's original fixed trace does not recognize the spawn command; the boot image's dispatcher reaches spawn only at the spawn family's own states.
- `allSpawnErrors_complete` — Bookkeeping: the list of spawn errors names every possible spawn error.
- `allSpawnErrors_codes_distinct` — Every spawn error has its own distinct numeric code.
- `decodeSpawnErrorCode_spawnErrorCode` — Decoding a spawn error's code gives back exactly that error.
- `spawnOracleSeed_authoritativeRuntimeWellFormed` — The test vectors start from a kernel state that satisfies the full rulebook.
- `spawn_vectors_pass` — Every test vector behaves as expected on the sample boot plan: each failure point, exhausted counters, stale and malformed handles, a re-granted spawn permission, isolation of other programs, the child presenting the parent's handle, and no identity reuse after termination; every refusal leaves the observed state unchanged.
