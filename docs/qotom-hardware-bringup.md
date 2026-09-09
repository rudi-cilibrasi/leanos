# First physical boot: Qotom J1900 rejection

The first `hardware` scenario is **controlled rejection**, not successful CPL3
execution. The opt-in manifest is [hardware/manifest.json](../hardware/manifest.json).
It is separate from the release-blocking emulator matrix: ordinary TCG/KVM
commands neither select hardware rows nor contact this machine.
See [ADR 0016](adr/0016-physical-rejection-evidence.md) for the trust boundary.

## Observed result

On 2026-09-09 the pinned image booted from USB on the reference Qotom and emitted:

```text
LEANOS/10 BOOT target=x86_64-q35 subjects=2 schedule=blocking-ipc controls=wp,smep,smap
LEANOS/3 FINAL status=FAIL reason=dma-identity
```

The 180-second capture retained 10 non-protocol prefix bytes, these exact 135
kernel bytes, and **no bytes afterward for 150.68 seconds**. The serial-only
kernel left the display showing `GRUB`; that display alone was not a loader
failure. A previous attempt included a reset during capture and was rejected
for post-terminal bytes. Neither that attempt nor timeout alone is a pass.

The compact [observation](../hardware/observations/qotom-20260909/bundle.json)
retains the unmodified raw stream and timestamped events. Its provenance says
`imported-observation`: it was captured before the integrated runner existed.
The exact [original capture implementation](../hardware/observations/qotom-20260909/implementation.py)
is archived, and its digest matches the observation's provenance. The new
verifier recomputes the classification instead of trusting the original result.
The original private result's digest is retained; its local adapter pathname
is not published. Capture duration is reconstructed from the original
last-event elapsed time plus reported quiet time, and checked against UTC.

Verify offline, without opening a serial device:

```sh
python3 scripts/hardware-evidence.py verify hardware/observations/qotom-20260909
```

This checks the profile, schema, payload hashes, event reconstruction, timing,
normalization, and exact protocol. `artifacts_checked: false` means only the
artifact digests bound in the repository manifest were checked. To independently
rehash actual image and ELF bytes as well:

```sh
python3 scripts/hardware-evidence.py verify hardware/observations/qotom-20260909 \
  --iso build/boot/leanos-0.1.0-x86_64.iso --elf build/boot/leanos.elf
```

## Bounded machine identity and expected reason

The [reviewed inventory](../hardware/profiles/qotom-j1900-clbtm210-v1.json)
records a Celeron J1900 (family 6/model 55/stepping 8), 8 GiB RAM, four enabled
processors, AMI Aptio CRB board string, CLBTM210 firmware dated 2015-06-01,
all 15 observed PCI functions, physical COM1, USB medium, and capture cabling.
The enclosure is operator-identified as Qotom. SMBIOS does not expose a useful
case model or board revision; those unknowns are explicit, not inferred.
This evidence describes this observed machine, not every J1900 or Qotom product.

The first PCI function is `8086:0f00` at `00:00.0`, class `060000`.
At source `1cc62dbb6e365b8b00716c316c927d9dc6db8f9a`, `kernel_main` prints
BOOT then calls `quarantine_q35_pci_dma`, whose first expected identity is
`8086:29c0`. It rejects with `dma-identity` before writing that function's PCI
Command register, topology admission, or user entry. This reason was declared
before the physical boot. The Qotom's missing SMAP and four enabled processors
would also prevent later admission; they do not make another transcript pass.

No admission constant, serial protocol, QEMU runner, or security claim is changed.
The manifest pins **one exact source revision, ISO, ELF, and toolchain profile**.
An updated image needs a reviewed row/profile update after examining its check
order and expected terminal sequence; overriding the expected reason at the CLI
is intentionally unsupported.

## Build and prepare the USB

The observed image was built on Ubuntu 24.04 with Lean 4.32.0, GCC 13.3.0,
and the `gcc-reference` profile. Build the pinned source in a separate checkout
so later capture-tool commits cannot silently change the artifact identity:

```sh
git worktree add --detach build/hardware-source 1cc62dbb6e365b8b00716c316c927d9dc6db8f9a
(cd build/hardware-source && LEANOS_EVIDENCE_TIER=pr LEANOS_BUILD_JOBS=4 ./scripts/build-image.sh)
```

Use its `build/boot` directory for the artifact arguments below. The observed
ISO SHA-256 is `bef7bf6873938263dc9dfa2b280bd93065ad10f06e59b0273968626e4eac12fb`;
ELF SHA-256 is `2b961990117b01ec9fa4480998ac71e6cd776ef90b841389a96d89b7aaa51ae9`.
The selected toolchain JSON is also pinned. Different tool/package bytes may
produce a different artifact; do not replace the expected digest just to pass.
The canonical QEMU smoke test passed before the physical observation.

The observed USB is Alcor `058f:6387`, 62,914,560,000 bytes, 512-byte sectors.
FreeBSD exposed it as `/dev/da0`; the internal Hoodisk SSD was `/dev/ada0`.
These names are observations, not persistent identifiers. Before writing,
use `sudo usbconfig dump_device_desc`, `sudo camcontrol devlist`,
`geom disk list`, and `mount` to identify the intended medium by serial and
capacity and confirm it is unmounted. Never use a disk name inferred only
from an earlier session. Writing the image replaces the existing USB contents.

For this exact ISO (21,944,320 bytes / 42,860 sectors), after independently
confirming `/dev/da0` is the intended disposable stick and transferring the ISO:

```sh
# On FreeBSD; verify the ISO's SHA-256 before this step.
# Keep the backup on the internal filesystem, not on the USB being written.
sudo dd if=/dev/da0 of=/var/tmp/usb-original-prefix.bin bs=512 count=42860
sudo dd if=/tmp/leanos.iso of=/dev/da0 bs=1m conv=fsync
sudo dd if=/dev/da0 of=/var/tmp/usb-readback.bin bs=512 count=42860
sha256 /var/tmp/usb-readback.bin
```

The readback must equal the manifest's ISO hash. The prefix backup restores
only the bytes written by this exact image; preserve a full backup if other
changes to the stick are planned. The observed write was read back and matched.
The image has a GRUB hybrid MBR and a BIOS El Torito entry, built with
`grub-mkrescue -d /usr/lib/grub/i386-pc`; it is not a UEFI boot image.

## Firmware and serial setup

Use the Qotom's **Win7 Legacy** compatibility mode and select the USB's legacy
boot entry. Those labels name firmware modes, not an OS requirement. The first
attempt selected the internal FreeBSD UEFI entry instead and produced no LeanOS
protocol. Record any different firmware setting as a new observation context.

Connection: Linux capture host → FTDI FT232R USB-to-RS-232 cable (`0403:6001`)
→ DB9 female/female null-modem adapter → target COM1 (`0x3f8`, IRQ 4).
The null-modem adapter's make/model was not supplied. A prior test compared
distinct messages exactly in both directions using FreeBSD `/dev/cuau0`.
Use 38400 baud, 8N1, raw input, echo off, and no RTS/CTS or XON/XOFF flow control.
The integrated runner configures these settings itself. Use the adapter's
actual stable `/dev/serial/by-id/...` path; serial identifiers are redacted
from committed inventory. Close other readers of the port.

FreeBSD callout access can use the `dialer` group; Linux access can use `dialout`.
New group membership takes effect in a new login. On FreeBSD, use sudo to set
`/dev/cuau0.init` if doing a preparatory link test: fresh opens inherit that
initial state. Those settings are runtime-only. LeanOS initializes COM1 itself.

## Capture from reset

In terminal A, from the current repository (not the old source worktree):

```sh
python3 scripts/hardware-evidence.py capture \
  --scenario qotom-j1900-clbtm210-v1 \
  --source-revision 1cc62dbb6e365b8b00716c316c927d9dc6db8f9a \
  --iso build/boot/leanos-0.1.0-x86_64.iso \
  --elf build/boot/leanos.elf --toolchain build/boot/TOOLCHAIN_PROFILE.json \
  --protocol build/boot/serial-protocol.tsv \
  --device /dev/serial/by-id/YOUR_ADAPTER \
  --operator 'operator name and firmware selection confirmation' \
  --output build/hardware/attempt-01
```

Use sudo if needed for serial access. The output directory must be new.
The runner verifies all supplied artifacts before opening the serial port.
After it prints READY, use terminal B (with the same filesystem permissions):

```sh
python3 scripts/hardware-evidence.py mark-reset build/hardware/attempt-01
# Immediately issue `sudo shutdown -r now` through the existing FreeBSD SSH
# session, or physically reset the machine, then select the legacy USB entry.
```

`mark-reset` records an **operator assertion**, not independent proof of reset.
No command supplied by a manifest is executed. The runner does not reboot,
write boot media, contact a host, or change firmware. The kernel bytes must
follow the reset declaration; a missing/late declaration cannot pass.
Leave the target untouched until the runner exits after 180 seconds. A bare
GRUB screen is not a reason to reset while recording. After capture completes,
reset and select the internal SSD's FreeBSD boot entry to recover SSH.

Repeat `verify` on the resulting directory. `result.json` is a convenience
report, never the authority for verification. Partial/infrastructure failures
retain available raw logs plus a non-passing report; they are not valid complete
bundles. A serial-device error, byte limit, timeout, wrong source/artifact,
wrong rejection, malformed transcript, unexpected success/user-entry, or
post-terminal byte each fails explicitly. Every unrecognized kernel record
also fails exact comparison, including scheduler/timer/syscall output.

Only CRLF pairs are normalized to LF. All bytes before the first `LEANOS/`
are retained as unclassified pre-kernel data, including garbled firmware text.
From the first marker onward, the complete stream must equal the manifest's
two lines. At least 10 seconds after the final byte must be observed with no
more bytes. Silence without the two records never passes.

## Bundle and publication

[The JSON schema](../hardware/bundle.schema.json) defines metadata fields.
The standard-library verifier implements only the schema keywords that file
uses and rejects unsupported keywords, duplicate keys, nonfinite numbers,
unknown fields, unsafe files, missing payloads, and hash drift. It also checks
semantic constraints not expressible there: repository profile equality,
artifact/source binding, contiguous event offsets and bytes, monotonic/UTC
consistency, reset timing, and exact transcript classification. Live bundles
contain `reset.json`; its declaration must match metadata.

Complete bundles contain the reviewed profile/inventory, exact selected
toolchain JSON, raw and normalized streams, per-chunk events, capture settings,
source/artifact digests, operator metadata, and the exact capture-implementation
source and digest. The implementation file is retained as data and is never
executed by verification.
The image/ELF may be retained alongside or in an external artifact archive;
the compact checked observation binds their exact hashes and accepts them as
explicit verifier inputs. There is no network download during verification.

Serialization uses sorted JSON keys. Repeating verification is deterministic;
observation timestamps, event chunk boundaries, operator text, and the resulting
hashes are explicitly observation-dependent. Hashes detect accidental drift,
not malicious fabrication by an operator who controls capture and metadata.

Before publication, review serials, UUIDs, MAC/IP addresses, and operator names.
The committed inventory omits unrelated mounts and network data, redacts device
serials, and retains all observed PCI identities and technical firmware data.
The actual serial bytes/events are never edited for redaction; if they contain
sensitive data, retain them privately with hashes and report the publication
limitation rather than presenting edited bytes as the original capture.

## Automated recovery follow-up

A fully unattended loop needs both directions: a one-time selection of LeanOS
from FreeBSD, then recovery back to FreeBSD after the observation completes.
An optional timed reset combined with a writable bootloader one-time entry and
FreeBSD as the persistent default is a candidate. Direct chainloading after
kernel execution would instead require a defined boot handoff and restoration
of the CPU/device state expected by the next loader.

Neither recovery mechanism is part of this rejection profile. Its kernel must
remain in the terminal state until reset, and its capture must finish before
reset bytes arrive. The present ISO filesystem does not provide the writable
boot-selection state needed for that proposed loop. An automated lab mode would
need a separate reviewed boot-medium layout and completion/reset contract;
the Qotom's firmware support for a suitable one-time selection is not assumed.

## Relationship to the offline classifier work

[PR #326](https://github.com/rudi-cilibrasi/leanos/pull/326) develops a broader
offline typed-rejection classifier with generated pre-admission reason metadata.
This contribution supplies the physical observation and bounded live stream
capture for a **closed historical profile**. The actual booted source predates
that metadata: its generated protocol table contains record identities but not
the newer pre-admission reason lists. Relabeling the captured source revision
or synthesizing a newer table as if it came from the old build would invalidate
provenance, so this profile pins the reviewed exact old bytes and vocabulary.
It does not introduce a general runtime-reason allowlist.

The full raw capture also includes non-UTF-8 firmware-prefix bytes. They stay in
the observation, with the kernel boundary inferred from the first protocol
marker. A future integration with the broader classifier must preserve that
raw envelope and timing, explicitly bind any extracted kernel-only stream, and
use artifacts carrying the matching generated reason contract. Until then,
this manifest intentionally accepts only the already reviewed historical
source/artifact combination; it cannot certify arbitrary new images.
