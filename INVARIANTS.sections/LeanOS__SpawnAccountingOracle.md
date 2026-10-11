# Charged spawn command encoding and adversarial test vectors

This section fixes exact word encodings for giving memory to a child and ending a child, and checks charged spawning against hostile and limit-exhausting requests on a realistic kernel state. It is the general test boundary inside the Lean model; user programs cannot issue these commands, and the boot image's dispatcher reaches the same encodings only at the spawn family's own states.

- `decodeChild_encodeGrant` — A memory-grant command with a nonzero frame count decodes back to exactly that grant.
- `decodeChild_encodeTerminate` — An end-child command decodes back to exactly that request.
- `encodeGrant_decodeChild` — Any words that decode to a memory grant are exactly the standard encoding of it, so there is only one way to write each grant.
- `encodeTerminate_decodeChild` — Any words that decode to an end-child request are exactly its standard encoding.
- `boot_dispatcher_rejects_child_tags` — The command decoder of the dispatcher's original fixed trace does not know either new command; the boot image's dispatcher reaches them only at the spawn family's own states.
- `childSpawnErrorCodes_distinct` — Every charged-spawn refusal reason has its own code.
- `frameGrantErrorCodes_distinct` — Every memory-grant refusal reason has its own code.
- `controlDenialCodes_distinct` — Every control-handle refusal reason has its own code.
- `allChildSpawnErrors_complete` — The list of charged-spawn refusal reasons is complete.
- `allControlDenials_complete` — The list of control-handle refusal reasons is complete.
- `allFrameGrantErrors_complete` — The list of memory-grant refusal reasons is complete.
- `decodeChildSpawnErrorCode_code` — Reading a charged-spawn refusal code back gives exactly the original reason.
- `decodeFrameGrantErrorCode_code` — Reading a memory-grant refusal code back gives exactly the original reason.
- `decodeControlDenialCode_code` — Reading a control-handle refusal code back gives exactly the original reason.
- `childErrorCodes_injective` — No two refusal reasons of the same command share a code.
- `child_vectors_pass` — Every test vector passes: both kinds of limit exhaustion, a memory grant and its return, cleanup when a child ends, old handles refused after the child ends and after its slot is reused, isolation of other subjects, and the earlier spawn vectors through the charged path.
