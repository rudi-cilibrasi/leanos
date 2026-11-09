# USB mass storage (lab)

Beside the USB keyboard ([usb-keyboard.md](usb-keyboard.md)) and mouse
([usb-mouse.md](usb-mouse.md)), LeanOS reads a USB mass-storage device
through a Lean device program on the xHCI controller: bulk-only transport
(BOT) with the SCSI transparent command set, read-only. It is written in the
same instruction-set DSL (`LeanOS/Wifi/Bytecode.lean`), runs on the same
generated executor and shares the controller, hub and enumeration code of
the HID programs. The other block reader, AHCI, is
[storage-ahci.md](storage-ahci.md).

| Module | Contents |
| --- | --- |
| `LeanOS/Usb/Xhci.lean` | Controller, command and event rings, transfer rings (`Ring`, with a TRB count), Enable Slot / Address Device, control transfers; `Layout.bulkBuf`, the scratch of the bulk buffers |
| `LeanOS/Usb/Hid.lean` | Shared: root port scan, USB 2.0 hub support ([usb-hub.md](usb-hub.md)), `findInterface` (the configuration-descriptor walk by interface class, subclass and protocol, with per-class endpoint handling), `attachWith` (bring-up and enumeration with a per-class acceptance routine) |
| `LeanOS/Usb/MassStorage.lean` | Interface match, bulk endpoints, BOT, the SCSI commands, the `MSC` records, the `program` entry point |
| `LeanOS/Usb/Fat32.lean` | One file from a FAT32 volume: the MBR, the BPB, the 8.3 path through the directories and the file's cluster chain (`fileProgram`; [below](#reading-a-file-fat32)) |

## What the program does

1. **Discovery.** It brings the controller up and enumerates like the HID
   programs: the first hub on a root port is configured and its ports are
   searched, then the root ports. It accepts the first device with an
   interface of class 8 (mass storage), subclass 6 (SCSI transparent
   command set) and protocol 0x50 (bulk-only transport) that has a bulk IN
   and a bulk OUT endpoint; their addresses and max packet sizes come from
   the endpoint descriptors. Other devices are addressed, passed over and
   their slots disabled again.
2. **Endpoints.** SET_CONFIGURATION, then one Configure Endpoint command for
   bulk IN (DCI 2n + 1) and bulk OUT (DCI 2n), each on its own transfer ring.
3. **Transport.** Each command is a 31-byte CBW on bulk OUT (signature
   0x43425355, a fresh tag per command counting from 1, the data transfer
   length, the direction flag, LUN 0, the command block length and the CDB),
   then the data stage on bulk IN (one Normal TRB into the data buffer), then
   a 13-byte CSW on bulk IN. The CSW must be 13 bytes, carry the signature
   0x53425355 and the command's tag, and have status 0 (passed) or 1
   (failed); status 2 (phase error) or more stops the program.
   A device may STALL bulk IN in the data stage when it has less data than
   asked, or none (BOT 1.0 §6.7.2), and real sticks do so for a failed READ.
   The program then recovers the endpoint and reads the CSW, which reports
   the failure. Recovery is Reset Endpoint (Halted to Stopped), then Set TR
   Dequeue Pointer to the ring's next TRB with its cycle state (past the
   stalled TD), then CLEAR_FEATURE(ENDPOINT_HALT) on the device, which resets
   its data toggle. A stalled CSW is recovered the same way and read once
   more.
4. **Commands.** INQUIRY (36 bytes); TEST UNIT READY up to 10 times, 100 ms
   apart, each failure followed by REQUEST SENSE (many devices report a unit
   attention after a reset); READ CAPACITY(10); READ(10) of LBAs 0–3 in one
   command, of the middle LBA (blocks / 2) and of the last two LBAs in one
   command; then READ(10) of the LBA after the last, which the device must
   fail, followed by REQUEST SENSE.
5. **Stop.** The controller is halted (Run/Stop cleared, HCHalted awaited)
   at the end, so nothing is transferred after the program; it then halts
   with status 0. A failed step prints an `MSC error=` record, halts the
   controller the same way and fails with code 0x7F23.

Each wait for a transfer event is bounded (2 s without an event, and at most
32 unrelated events). Blocks of up to 4096 bytes are supported (four of them
fill the 16 KiB data buffer); a device that needs READ CAPACITY(16) (last
LBA 0xFFFFFFFF) is refused. BOT reset recovery (the class-specific reset and
clearing both halts) is not implemented, so the program stops with an error
record in these cases:

* a stalled CBW;
* a CSW that stalls twice;
* a phase error.

The Set TR Dequeue Pointer command's parameter is a bus address inside the bulk
ring. The executor's per-store descriptor-map check (ADR 0021) admits it as it
admits the transfer TRBs, so the policies are unchanged.

## Records

The program prints these records on COM1, each one line (the lab kernel's
print hook, `hardware/lab/qotom-wifi.c.inc`, assembles a record from several
print words). `<dec>` is unsigned decimal; hex is lower case.

```text
LEANOS-LAB/1 MSC ready vendor=0x<4 hex> product=0x<4 hex>
LEANOS-LAB/1 MSC configured bulk-in=0x<2 hex> in-max-packet=<dec> bulk-out=0x<2 hex> out-max-packet=<dec>
LEANOS-LAB/1 MSC inquiry type=0x<2 hex> removable=<0|1> vendor="<text>" product="<text>" revision="<text>"
LEANOS-LAB/1 MSC csw step=<step> status=<dec> residue=<dec>
LEANOS-LAB/1 MSC sense after=<step> key=0x<2 hex> asc=0x<2 hex> ascq=0x<2 hex>
LEANOS-LAB/1 MSC stall-cleared step=<step> stage=<data|csw> endpoint=0x<2 hex>
LEANOS-LAB/1 MSC unit-ready attempts=<dec>
LEANOS-LAB/1 MSC capacity blocks=<dec> block-bytes=<dec>
LEANOS-LAB/1 MSC block lba=<dec> head=<32 hex> fnv1a=0x<8 hex>
LEANOS-LAB/1 MSC done blocks-read=<dec>
LEANOS-LAB/1 MSC error=<step> stage=<stage> reason=<reason> detail=0x<8 hex>
```

* `ready`: idVendor and idProduct of the accepted device.
* `configured`: the bulk endpoints' addresses and wMaxPacketSize.
* `inquiry`: the peripheral device type (byte 0, bits 0–4), RMB (byte 1,
  bit 7), and the T10 vendor (bytes 8–15), product (16–31) and revision
  (32–35) of the standard INQUIRY data, without their trailing spaces; a
  byte outside printable ASCII, `"` and `\` print as `.`, a zero byte as a
  space.
* `csw`: a command whose CSW reported status 1 (failed); `residue` is its
  dCSWDataResidue. Printed before the step decides what to do: TEST UNIT
  READY retries, the read past the end expects it, any other step stops.
* `sense`: REQUEST SENSE after a failed command, `after` naming the step it
  explains; key, ASC and ASCQ from fixed-format (0x70, 0x71) or
  descriptor-format (0x72, 0x73) sense data.
* `stall-cleared`: the device stalled bulk IN in the data stage or the CSW
  stage of `step`, and the endpoint was recovered (Reset Endpoint, Set TR
  Dequeue Pointer, CLEAR_FEATURE(ENDPOINT_HALT)); the CSW is read next.
* `unit-ready`: TEST UNIT READY passed on this attempt.
* `capacity`: READ CAPACITY(10)'s last LBA + 1 and block length.
* `block`: one block read. `head` is its first 16 bytes in order, two hex
  digits each. `fnv1a` is the 32-bit FNV-1a hash of all its `block-bytes`
  bytes: start from h = 0x811c9dc5 and, for each byte b in order, set
  h = (h XOR b) × 0x01000193 mod 2^32.
* `done`: every step passed; the number of `block` records.
* `error`: the program stopped. `<step>` is one of `attach`, `configure`,
  `inquiry`, `unit-ready`, `capacity`, `read`, `read-past-end`, `sense`;
  `<stage>` is `none`, `cbw`, `data` or `csw` (where in the command); the
  reasons are:

| Reason | Meaning | Detail |
| --- | --- | --- |
| `no-device` | no device with a BOT SCSI interface and both bulk endpoints | 0 |
| `timeout` | no transfer event within 2 s | 0x100 |
| `stall` | the endpoint stalled | completion code 6 |
| `transfer` | another completion code | the code |
| `csw-length` | the CSW was shorter than 13 bytes | bytes missing |
| `csw-signature` | wrong dCSWSignature | the signature |
| `csw-tag` | dCSWTag is not the CBW's | the tag |
| `phase-error` | bCSWStatus 2 | 2 |
| `csw-status` | bCSWStatus above 2 | the status |
| `failed` | bCSWStatus 1 where the step needs success | 1 |
| `not-ready` | TEST UNIT READY failed every attempt | the attempts |
| `capacity` | last LBA 0xFFFFFFFF, or block length 0 or above 4096 | the value |
| `short-read` | a data stage moved fewer bytes than asked (transfer residual or dCSWDataResidue) | bytes missing |
| `passed-past-end` | the READ(10) past the last LBA passed | 0 |

The enumeration's own failures (controller bring-up, commands, control
transfers) end the program with the xHCI driver's fail codes (0x7Fxx), as
for the HID programs.

## Rings, buffers and confinement

The xHCI policies' descriptor maps (`Xhci.descriptorMap`, `qotomXhciPolicy`,
`q35XhciPolicy`) fix the scratch regions whose pointer fields may hold only
scratch bus addresses; one of them is the interrupt-ring region of
`ringTrbs` (64) TRBs that the HID programs use for their interrupt IN ring.
The mass-storage program uses no interrupt endpoint and splits that region
into its two bulk rings, each of 32 TRBs closed by its own Link TRB
(`Xhci.Ring.trbs`):

| Ring | Scratch (Bay Trail / qemu-xhci) | TRBs |
| --- | --- | --- |
| bulk OUT (ring id 6) | 0x25000–0x251FF / 0x3800–0x39FF | 31 + Link |
| bulk IN (ring id 7) | 0x25200–0x253FF / 0x3A00–0x3BFF | 31 + Link |

The endpoint contexts' TR Dequeue Pointers lie in the input context's
dequeue-pointer region, already in the map. The CBW (`bulkBuf`, 31 bytes),
the CSW (`bulkBuf + 0x40`, 13 bytes) and the data buffer (`bulkBuf + 0x100`,
16 KiB) are plain scratch at `bulkBuf` = 0x8000 in both layouts, below the
Bay Trail scratchpad pages and above the qemu-xhci driver's state; the
controller reads or writes them but never follows them as pointers, so they
need no descriptor. The Normal TRBs that point at them hold scratch bus
addresses, which the executor checks on every store into the ring region.

So the program touches only the registers, address sinks and descriptor
regions the keyboard and mouse touch, and both images pass
`DeviceProgramConfinement.admissible` under the existing xHCI policies,
unchanged: no policy, lab profile or pin changed for it. On qemu-xhci the
bulk buffers lie outside the four pages the q35 device service maps for the
keyboard through VT-d; the mass-storage program runs only in the lab kernel,
whose scratch is identity-mapped and not behind an IOMMU.

## Generator targets

`leanos-wifi-gen msc` builds the program for the Qotom's Bay Trail
controller and `leanos-wifi-gen msc-q35` for QEMU's `qemu-xhci`; both are
emitted only after the static confinement check
([device-program-confinement.md](device-program-confinement.md)), and
`scripts/check-device-programs.sh` generates `msc` with the other
firmware-free programs. `lake exe leanos-usb-msc-report` checks the block
records (head, FNV-1a) and the big-endian capacity parsing in simulation.

## QEMU

`python3 scripts/run-q35-device-lab.py --msc` builds `msc-q35` into the q35
device-lab kernel, writes a raw disk image and boots QEMU q35 with a
`qemu-xhci`, a hub on QEMU's root port 1 and a `usb-storage` on hub port 1
backed by the image (`-drive if=none,format=raw,readonly=on` and
`-device usb-storage,drive=...`). The image has 8192 blocks of 512 bytes
(4 MiB); block n starts with the 16 ASCII bytes `LBA<n as 8 hex digits>-MSC`
and a newline, and its other 496 bytes are the first bytes of the SHA-256
digests of `leanos-msc <n> <k>` for k = 0, 1, …, so every block differs and a
misread block or offset shows.

The check requires the ready record to name QEMU's storage device
(46f4:0001), the endpoints to be 0x81 and 0x02 with max packet 64 (full
speed, behind QEMU's full-speed hub), the INQUIRY record to name vendor
`QEMU` and product `QEMU HARDDISK`, a unit-ready record, the capacity to be
the image's (8192 blocks of 512 bytes), exactly the block records of LBAs 0,
1, 2, 3, 4096, 8190 and 8191 with heads and hashes equal to the script's own
computation over the image, a failed CSW (status 1) for the read past the
end with sense key 0x05 (ILLEGAL REQUEST) and ASC 0x21 (LBA out of range),
the done record, no error record and the program's status 0.

`--msc --root-port` puts the storage on QEMU's root port 2 instead and a
`usb-kbd` alone behind the hub. qemu-xhci numbers its USB 3 ports 1–4 and its
USB 2 ports 5–8 and attaches a device to the USB 3 half of a QEMU port when
it can, so the full-speed hub is xHCI port 5 (as in every scenario) and the
storage enumerates at SuperSpeed on xHCI port 2, with bulk max packet 1024.
The hub search passes over the SuperSpeed port 2 without addressing the
storage (`HUB passed-over root-port=2 speed=super`). The driver then
configures the hub and passes over the keyboard (it has no mass-storage
interface). Last, it skips the hub's port and accepts the storage on port
2. The same records are required, with max packet 1024, and the keyboard's
rejection. `--msc --hub-port 7` puts the storage on hub port 7 and a decoy
keyboard on port 1, and also checks the hub records
([usb-hub.md](usb-hub.md)). `scripts/check.sh` runs all
three after the mouse scenarios.

An excerpt of the hub scenario's transcript:

```text
LEANOS-LAB/1 MSC ready vendor=0x46f4 product=0x0001
LEANOS-LAB/1 MSC configured bulk-in=0x81 in-max-packet=64 bulk-out=0x02 out-max-packet=64
LEANOS-LAB/1 MSC inquiry type=0x00 removable=0 vendor="QEMU" product="QEMU HARDDISK" revision="2.5+"
LEANOS-LAB/1 MSC unit-ready attempts=1
LEANOS-LAB/1 MSC capacity blocks=8192 block-bytes=512
LEANOS-LAB/1 MSC block lba=0 head=4c424130303030303030302d4d53430a fnv1a=0x7980d3b9
LEANOS-LAB/1 MSC block lba=4096 head=4c424130303030313030302d4d53430a fnv1a=0xbed461e5
LEANOS-LAB/1 MSC block lba=8191 head=4c424130303030316666662d4d53430a fnv1a=0xc10d51a4
LEANOS-LAB/1 MSC csw step=read-past-end status=1 residue=512
LEANOS-LAB/1 MSC sense after=read-past-end key=0x05 asc=0x21 ascq=0x00
LEANOS-LAB/1 MSC done blocks-read=7
LEANOS-LAB/1 WIFI-END status=0 code=0x00000000
```

QEMU's `usb-storage` passes the first TEST UNIT READY, so the retry path
(failed CSW, REQUEST SENSE, retry) is not exercised there. For the read past
the end it completes the data stage without a stall and then reports the
failed CSW with dCSWDataResidue 512, so no stall needs clearing.

On the Qotom the `msc` image is built and booted like the keyboard's
([usb-keyboard.md](usb-keyboard.md), "Trying it") with
`lake exe leanos-wifi-gen msc build/wifi/msc.bin` and
`--lab-program build/wifi/msc.bin`.

It ran there on 2026-11-08, on the old lab stick (Alcor `058f:6387`,
122880000 blocks of 512 bytes) on a root port, through the hub search
([observation](../hardware/lab/observations/qotom-usb-20261108/README.md)):

* **INQUIRY, capacity and blocks.** INQUIRY and the capacity matched FreeBSD's
  view of the same stick. All seven `MSC block` records were byte-identical to
  FreeBSD's `dd` of the same LBAs.
* **The retry path.** The first TEST UNIT READY failed with UNIT ATTENTION
  (06/28/00), and the second passed. This was the first run of the retry path.
* **The read past the end.** The stick STALLs the bulk-IN endpoint in the data
  stage, and the program stopped with
  `MSC error=read-past-end stage=data reason=stall`. With stall recovery
  (issue #631), the same stick, read through the hub, gives
  `MSC stall-cleared step=read-past-end stage=data endpoint=0x82`, then the
  failed CSW (`status=1 residue=512`), then sense 05/21/00 (ILLEGAL REQUEST,
  LBA out of range), and `MSC done blocks-read=7`.

## Reading a file (FAT32)

`LeanOS/Usb/Fat32.lean` builds on the program above. It reuses the same
enumeration, endpoints, INQUIRY, TEST UNIT READY and READ CAPACITY(10), then
reads one file from the device's first FAT32 partition, one 512-byte block at
a time:

1. **MBR.** LBA 0 must end in 0x55 0xAA. Each used entry of the four is
   printed, and the first of type 0x0B or 0x0C is the volume.
2. **BPB.** The partition's first block must be a FAT32 BPB with 512-byte
   sectors (the device's block length too), a power-of-two cluster size, one
   or two FATs, FATSz16 = 0 and FATSz32 ≠ 0. The cluster limit is
   (TotSec32 − blocks before the data) / SecPerClus + 2, and at most what the
   FAT can describe. The root cluster must be inside it.
3. **Path.** Each component of `LEANOS_MSC_FILE` (8.3 short names, matched as
   the directory entry stores them, upper case and space-padded) is searched
   along its directory's cluster chain. Deleted, long-name and volume-label
   entries are skipped. All components but the last must be directories, and
   the last must be a file.
4. **File.** The file's chain is followed, and exactly its size is hashed with
   FNV-1a (as the `block` records). The record gives the size, the first 16
   bytes, the hash and the clusters read.

**Bounds.** Every cluster number, in a directory entry or the FAT, is checked
against the volume before it is used. A chain stops at 0x0FFFFFF8 or after
`maxChain` clusters, so a corrupt volume ends in an `MSC error=` record (steps
`mbr`, `volume`, `lookup`, `file`; reasons `no-partition`, `not-fat32`,
`not-found`, `bad-cluster`, `wrong-kind`, `chain-too-long`, `chain-short`)
instead of a read outside it.

**One subroutine for every block read.** The ten block reads call a single
copy of the BOT READ(10) (`call`/`ret`). One inlined BOT command, with its
stall recovery, is hundreds of instructions.

```text
LEANOS-LAB/1 MSC mbr partition=<n> type=0x<2 hex> active=<0|1> lba=<dec> blocks=<dec>
LEANOS-LAB/1 MSC fat32 sectors-per-cluster=<n> fats=<n> reserved=<n> fat-blocks=<n> root-cluster=<n>
LEANOS-LAB/1 MSC fat found component=<i> attr=0x<2 hex> cluster=<dec> bytes=<dec>
LEANOS-LAB/1 MSC file bytes=<dec> head=<32 hex> fnv1a=0x<8 hex> clusters=<dec>
```

The generator targets are `msc-fat` and `msc-fat-q35`, with
`LEANOS_MSC_FILE=BOOT/GRUB/GRUB.CFG` by default. Both are admitted under the
unchanged xHCI policies.

`python3 scripts/run-q35-device-lab.py --fat`, in `scripts/check.sh`, builds
the disk with mtools: a non-FAT partition first, a 30-entry long-name
directory spanning several clusters, and the file's chain made
non-contiguous. It requires every record to equal the script's own reading of
the image.

**On the Qotom** (2026-11-08,
[observation](../hardware/lab/observations/qotom-usb-20261108/README.md),
`msc-fat32/`), the program read `/boot/grub/grub.cfg` from the old lab stick's
FAT32 partition, through the hub:

```text
MSC file bytes=7725 head=23204c61622d6f6e6c792042494f532f fnv1a=0x407c2dba clusters=16
```

That is the size, head and hash of FreeBSD's copy of the same file.

Not covered: writing, other transports (UAS, CBI),
READ CAPACITY(16), more than LUN 0, BOT reset recovery, a stall in QEMU
(its `usb-storage` never stalls, so recovery runs only on hardware), a
device-service (yield) form, long file names, FAT12/16, exFAT and other file
systems, GPT disks; the enumeration's limits (one
level of hub, polling; [usb-hub.md](usb-hub.md)) are the HID programs'. The shared Address Device gives
EP0 a max packet size of 8 at every speed but high speed (64); QEMU accepts
that at SuperSpeed, where a real device needs 512.
