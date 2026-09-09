# Bare-metal typed-rejection capture

This optional procedure records the first physical-machine LeanOS milestone: a
named machine reaches the existing platform-admission boundary, emits one exact
typed rejection on COM1, and remains fail-stopped. It does **not** claim CPL3
execution, generic hardware support, or refinement of the binary to the Lean
model.

The hardware tier is manual and non-blocking. Do not change a platform admission
constant to make a machine pass. A different rejection is diagnostic evidence,
not success.

## Trust boundary

The observation trusts the machine firmware (including SMM/SMI), CPU and
chipset, boot medium and loader, physical UART, capture adapter, capture host,
and operator procedure. The classifier proves only that the supplied bounded
bytes and artifacts match the declared manifest. It cannot prove what hardware
executed, that no bytes were lost, or that the observed image refines the source
or proofs.

## Before capture

1. Use a dedicated clean checkout at the manifest's 40-character
   `sourceRevision`. Build the canonical ISO and ELF without modifying the
   admitted q35 inventory or security claims. Record both SHA-256 digests.
2. Select one machine with legacy BIOS/CSM boot and a physical 16550-compatible
   COM1 UART at `0x3f8`. Record its exact model/revision, CPU, firmware version,
   relevant firmware settings, and PCI inventory. Redact serial numbers, asset
   tags, and hostnames; do not erase the technical platform identity.
3. Record the USB-to-serial adapter model and cabling. Configure the capture host
   for 38400 baud, 8 data bits, no parity, one stop bit, and no flow control.
4. Create a manifest accepted by
   `scripts/check-bare-metal-rejection.py`. `expectedPrefix` must list every
   expected pre-terminal protocol record in order and every identity must exist
   in the revision's generated `serial-protocol.tsv`. `expectedTerminal` must
   be the one generated rejection identity predicted from the recorded platform
   inventory. Record the generated protocol file's SHA-256 digest.
5. Write the verified ISO to removable media. Confirm its digest again after
   writing or retain an independently read-back image digest.

Example manifest shape (placeholder values are deliberately not valid evidence):

```json
{
  "schemaVersion": 1,
  "sourceRevision": "<40 lowercase hex characters>",
  "isoSha256": "<64 lowercase hex characters>",
  "elfSha256": "<64 lowercase hex characters>",
  "serialProtocolSha256": "<64 lowercase hex characters>",
  "expectedPrefix": ["LEANOS/1 SERIAL status=READY"],
  "expectedTerminal": "LEANOS/1 BOOTALLOC status=FAIL reason=platform-inventory",
  "machine": {
    "model": "<vendor model and board revision>",
    "cpu": "<processor model and stepping>",
    "firmware": "<firmware version and relevant settings>",
    "uart": "COM1 0x3f8 38400 8N1",
    "captureAdapter": "<adapter model and connection>"
  }
}
```

Each machine field is limited to 512 characters. The manifest is limited to 64
KiB and the serial capture to 1 MiB.

If firmware emits bytes before the first LeanOS record, retain them in the raw
capture. The manifest may additionally declare `firmwarePrefixBytes` (1–4096)
and `firmwarePrefixSha256` (the exact prefix's lowercase SHA-256). Both fields
are required together. This explicit observation metadata permits binary
firmware output; it cannot hide a LeanOS protocol marker, consume the entire
capture, or skip bytes after kernel output starts. The normalized transcript
excludes only this verified prefix; the raw digest covers every captured byte.
Do not change the expected kernel records or artifact/source identities to fit
an observation. Without these fields, every byte is treated as protocol text.

## Capture

1. Disconnect the machine from production networks and attach the capture host.
2. Start a raw, non-interpreting serial capture before reset. Use a bounded
   operator timer. Record the exact capture command, tool version, device path,
   timeout, operator identifier, and UTC start/end times alongside the bundle.
3. Boot the verified medium once. Do not type into the serial session.
4. After the expected terminal record, continue capture for the documented
   timeout to establish bounded absence of post-terminal output. A timeout alone
   is never success.
5. Stop capture, power-cycle or reset the target, and preserve the original raw
   bytes read-only.

Classify a copied snapshot of those bytes:

```sh
python3 scripts/check-bare-metal-rejection.py \
  machine.json build/leanos.iso build/leanos.elf serial.raw \
  --serial-protocol build/boot/serial-protocol.tsv \
  --source-revision "$(git rev-parse HEAD)" > classification.json
```

The only passing result is `exact-typed-rejection`. `wrong-rejection`,
`unexpected-success`, `malformed-protocol`, `post-terminal-output`,
`silence-timeout`, `digest-mismatch`, `manifest-invalid`, and `capture-failure`
are distinct non-passing diagnostics.

The passing classification binds both the raw capture and the canonical
CRLF/CR-to-LF normalized transcript with separate SHA-256 digests and byte
counts, plus the normalized line count. Generate the retained normalized file
with the same replacement rule and verify it against
`normalizedCaptureSha256` before publishing the bundle.

## Evidence bundle

Retain these files together without editing the raw capture:

- manifest and classification JSON;
- raw serial bytes and a separately named CRLF-to-LF normalized transcript;
- ISO, ELF, generated serial protocol, source revision, toolchain profile, and
  their SHA-256 digests;
- build command/configuration and capture command/configuration;
- bounded machine/firmware/PCI inventory and firmware-setting record;
- operator identifier, UTC observation interval, redaction note, and reset result.

Create a sorted SHA-256 manifest over every retained file and validate it before
publication. Observation timestamps and operator identity are explicitly
variable metadata; the classifier result and all content-derived digests must be
stable for identical inputs. Never commit physical serial numbers, hostnames,
credentials, or unrelated serial output.

Pass `--bundle-dir <new-directory>` to the classifier to atomically retain the
deterministic bundle core: the exact manifest, ISO, ELF, generated protocol, raw
and normalized captures, source revision, classification, and sorted
`SHA256SUMS`. The output directory must not already exist. The emitted core is
deterministic; the publication verifier intentionally waits for the variable
observation sidecar described below.

Keep the variable operator, capture-command, firmware-setting, inventory, and
reset metadata alongside this deterministic core as `observation.json`; those
observation records are not synthesized by the classifier. The sidecar must
conform to `docs/bare-metal-observation.schema.json`. Its timestamps use UTC
RFC 3339 date-times, and its bounded timeout is the same operator timer used for
the capture. Record a pseudonymous operator identifier and redaction note; do
not put a personal name, hostname, serial number, credential, or secret in the
sidecar.

Regenerate the sorted `SHA256SUMS` after adding `observation.json`, so it covers
every retained publication file. Then validate the exact inventory, digests,
reclassification, strict sidecar fields, bounds, UTC timestamps, and timestamp
ordering together before publication:

```sh
python3 scripts/verify-bare-metal-evidence-bundle.py <bundle-directory>
```

## Interpretation

A passing bundle is integration evidence that the named procedure observed the
exact versioned terminal protocol for the named artifacts and machine profile.
It does not establish final-binary correctness, firmware integrity, general
hardware compatibility, isolation, or a new admitted platform. Any later
hardware profile requires its own reviewed issue, model boundary, and evidence.
