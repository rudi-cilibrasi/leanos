# LeanOS USB programs on the Qotom — 2026-11-08

The mass-storage, keyboard and mouse device programs ran on the Qotom's Intel
Bay Trail xHCI controller (PCI 8086:0f35, 00:14.0), on real devices, through
the hub code of #623. Before this, the mass-storage and mouse programs had run
only in QEMU, and the keyboard had never received a physical key press on
hardware.

Each image was booted once from the internal disk with the one-shot request
([qotom-internal-boot.md](../../../../docs/qotom-internal-boot.md)): no USB
boot stick and no watchdog. Serial was captured on COM1 (38400 8N1). Each run
ended in the lab kernel's usual `FINAL status=FAIL
reason=qotom-platform-pending`, and the reset 30 s later booted FreeBSD on its
own.

The programs are #623's (commit 48d1ed5b), generated with
`lake exe leanos-wifi-gen` and built with
`scripts/build-qotom-recovery-lab.py --prepared-repo . --lab-program <bin>`.

## Devices

FreeBSD saw them as follows before the runs:

| Device | IDs | Speed | Attached to |
| --- | --- | --- | --- |
| Genesys hub (on the board) | `05e3:0610` | high | root port 4, 4 ports |
| Chicony keyboard | `04f2:0402` | low | hub port 4 |
| HP 310 mouse (PixArt) | `0461:4ef3`, IN `0x81`, max packet 4, bInterval 10 | low | hub port 3, later a root port |
| Alcor flash drive, the old lab stick (serial 11758C40) | `058f:6387` | high | root port 2, later hub port 3 |

## Mass storage (`msc/`)

| | |
| --- | --- |
| Program | `msc`, SHA-256 `4904cd560754fa74de7450d939472b5ba9fc471f596d867ed711288cba27b114` |
| Lab ELF | `4acbb0f91971ac5261675803647bd38188c49ce13fe81bf503a4f4a963998e9c` |
| Capture | `msc/serial.raw`, SHA-256 `9ccdbac5a5da1f7431d90a3c929fe666693c4a85da41c1264503eb68bdb26108` |

The run, step by step:

1. **The hub search** found the Genesys hub with the new code:
   - `HUB configured ports=4 power-on-wait-ms=250 tt-think-time=3`;
   - every port's status;
   - `route=0x00003 speed=low root-port=4 tt-slot=1 tt-port=3` for the mouse and `… tt-port=4` for the keyboard.

   It passed over both HID devices and found the stick on a root port.
2. **The bulk endpoints:** `bulk-in=0x82 in-max-packet=512 bulk-out=0x01 out-max-packet=512`.
3. **INQUIRY:** `vendor="Generic" product="Flash Disk" revision="8.07"`, removable. FreeBSD reports the same.
4. **TEST UNIT READY:** the first attempt returned CSW status 1, and sense was UNIT ATTENTION, 06/28/00 (the medium may have changed). The second attempt passed: `unit-ready attempts=2`.
   - This is the first run of the retry path; QEMU always passes the first attempt.
5. **READ CAPACITY(10):** `blocks=122880000 block-bytes=512`, as FreeBSD reports.
6. **READ(10)** of LBAs 0–3, 61440000, 122879998 and 122879999. All seven `MSC block` records are identical to `msc/freebsd-reference.txt`, FreeBSD's `dd` of the same blocks: the 16-byte heads and the FNV-1a hashes.
7. **The READ past the last LBA** ended the program:
   `MSC error=read-past-end stage=data reason=stall`, then `WIFI-END status=1 code=0x00007f23`.
   - The stick STALLs the bulk-IN endpoint in the data stage, which BOT §6.7.2 allows. QEMU never does this.
   - The program does not yet recover from a stall: issue #631.

### Stall recovery (`msc-stall-recovery/`, issue #631)

| | |
| --- | --- |
| Program | `msc` with stall recovery (#631), SHA-256 `483c173619d3b55f1e01c08483b4364b19c6f42d95c44629c70b157d97f15ba8` |
| Lab ELF | `186589858af4b3df0c449da7d17fff29b990576f10c57e88f75715a03bda1ac9` |
| Capture | `msc-stall-recovery/serial.raw`, SHA-256 `ceb1bb3ff553c196d8bb37f0df4574f65b6d1f64247c34325051bef2081217bb` |

The same stick, now on hub port 3 and reached through the hub
(`route=0x00003 speed=high`):

- The same INQUIRY, capacity and UNIT ATTENTION retry.
- The same seven blocks, identical to `msc/freebsd-reference.txt`.
- At the READ past the end, the stick stalled bulk IN again. The program recovered the endpoint and read the CSW:

```text
MSC stall-cleared step=read-past-end stage=data endpoint=0x82
MSC csw step=read-past-end status=1 residue=512
MSC sense after=read-past-end key=0x05 asc=0x21 ascq=0x00
MSC done blocks-read=7
WIFI-END status=0 code=0x00000000
```

The recovery is Reset Endpoint, Set TR Dequeue Pointer and
CLEAR_FEATURE(ENDPOINT_HALT). The sense data is ILLEGAL REQUEST with LOGICAL
BLOCK ADDRESS OUT OF RANGE: the answer SBC-3 requires, which QEMU gives without
stalling.

### A file from the stick's FAT32 volume (`msc-fat32/`)

| | |
| --- | --- |
| Program | `msc-fat` (`LeanOS/Usb/Fat32.lean`), `LEANOS_MSC_FILE=BOOT/GRUB/GRUB.CFG`, SHA-256 `0161ccc335c25aa1d8849106a688be6f06effbd79c439b8ef3043bb306b1216e` |
| Lab ELF | `b7d1bb28c79928563a297604076fcdc19b7b5b024f1059341e3b1ac4fac667f2` |
| Capture | `msc-fat32/serial.raw`, SHA-256 `0e913d52abf97f761dfec44ff843c45da0d72e2ee332dbfcd1225d5bd04e912e` |

The same stick, through the hub:

- **The MBR and the volume.** Its one partition is FAT32 at LBA 2048, 194560 blocks, active, as `gpart show da0` lists it. The program read its BPB.
- **The path.** It followed `BOOT` (cluster 3), `GRUB` (cluster 4) and `GRUB.CFG` (cluster 189179) by their 8.3 names.
- **The file.** It read the file's 16 clusters:

```text
MSC mbr partition=0 type=0x0c active=1 lba=2048 blocks=194560
MSC fat32 sectors-per-cluster=1 fats=2 reserved=32 fat-blocks=1497 root-cluster=2
MSC fat found component=0 attr=0x10 cluster=3 bytes=0
MSC fat found component=1 attr=0x10 cluster=4 bytes=0
MSC fat found component=2 attr=0x20 cluster=189179 bytes=7725
MSC file bytes=7725 head=23204c61622d6f6e6c792042494f532f fnv1a=0x407c2dba clusters=16
WIFI-END status=0 code=0x00000000
```

FreeBSD mounted the same partition read-only (`mount -t msdosfs -o ro
/dev/da0s1`). Its `boot/grub/grub.cfg` is 7725 bytes and begins
`# Lab-only BIOS/`, which is the head above. Its FNV-1a is `0x407c2dba` and its
SHA-256
`9e56eb78a05cabbfdc23de87d6a124c1d028dbdd2422505bffa482e4f32f0bac`.

### The same file with directory chains bounded (`msc-fat32-bounded/`, 2026-11-09)

| | |
| --- | --- |
| Program | `msc-fat`, with a directory's chain cut off at FAT's 65,536-entry limit and a file's at the volume's clusters, SHA-256 `6e7d0d10ce902ff94991a727d4dfa410073ef584416d167a900b57989f9edacc` |
| Lab ELF | `c0f7c266a3e2e48d8ffab5f43f776caf1a591bed6b68efe438a3fd5dc94813e1` |
| Capture | `msc-fat32-bounded/serial.raw`, SHA-256 `1ad50fce99229f3f9f682f7daab8519babb04a2a9ccbbf95d2d2da835061c168` |

Its MBR, volume, path and file records are identical to `msc-fat32/`'s, and
the program ended with `WIFI-END status=0`. The bounds change nothing on a
well-formed volume. What they stop, a looping directory chain among others,
is tested in QEMU (`run-q35-device-lab.py --fat-hostile`), since this stick
is only read.

## Keyboard (`keyboard/`)

| | |
| --- | --- |
| Program | `kbd`, `LEANOS_KBD_SECONDS=120`, SHA-256 `902dbff1d36a6daf04c1331b2958bdfead17e20b41e5059042944aeb0e67e484` |
| Lab ELF | `03bd0a1b2a7daf1fb573af7f57ec17105dbf6bc844806c7b3b1d7edad2f0e4ab` |
| Capture | `keyboard/serial.raw`, SHA-256 `6114b9ae37a3a8707a407cf0509e01e3b94e11246aca0be5da9353c746559bdf` |

The keyboard was on hub port 4, behind the high-speed hub's TT, with TT word `0x0401`. A person was asked to type `Hi LeanOS!`, Enter, Backspace. 14 keys came back, in order:

```text
H i space L : e a n o O S ! enter backspace
KBD reports=44   KBD session-end keys=14   WIFI-END status=0
```

- This is the first physical key press LeanOS has received on hardware. The 2026-09-27 observation had only idle reports.
- **Shift works:** the capitals and `!`.
- **The stray `:` and the extra `o`.** The `:` is Shift with the key next to `L`. The person also pressed Caps Lock, whose LED did not light: the program has no lock-key state yet (issue #632). That probably explains the lowercase `o` before `OS`.

### Lock keys (`keyboard-locks/`, issue #632)

| | |
| --- | --- |
| Program | `kbd` with lock keys (#632), `LEANOS_KBD_SECONDS=300`, SHA-256 `1e242e49586ef649135e83e2826b9a5438a90ae4245e50c653569c6348192435` |
| Lab ELF | `ac5570e9a9a612e8cfda6fd16850fe3c44a050dde3aa351643620990784da692` |
| Capture | `keyboard-locks/serial.raw`, SHA-256 `17fca58ebd047a0f4a1b7d3d36da017eb8f53b642f6ff00f083ca9d33d7c90d8` |

The same keyboard, behind the hub. The person was asked one step at a time and
confirmed what the Caps Lock LED showed after each step:

```text
KBD locks num=0 caps=1 scroll=0     ← the LED lit
HID control-done cc=1
KBD key=A                           ← "a" typed without Shift
KBD locks num=0 caps=0 scroll=0     ← the LED went out
HID control-done cc=1
KBD session-end keys=1   WIFI-END status=0
```

The program drives the LEDs with SET_REPORT(Output), queued on EP0 without
waiting. The keyboard acknowledged each one (`cc=1`), and the LED followed the
lock state.

## Mouse (`mouse/`, `mouse-buttons/`)

The mouse was on a root port, with no TT, for both captures.

| | `mouse/` | `mouse-buttons/` |
| --- | --- | --- |
| Program | `mouse`, `LEANOS_MOUSE_SECONDS=300`, SHA-256 `a7875516546d55e837ac9c24ef1e8fe9e27bb3e757d1854ac7e2f37f6ac5d942`, #623's code unchanged | the same session with an off-tree diagnostic trace, SHA-256 `5d733eb2869db60f744692ed175987cf6692db99f047d833c89d078e25834343` |
| Lab ELF | `6b70f00290e665c4c09669afec2f73710970a4a1cd671af9bea0090bfa575be5` | `135be1936f3000e77b781183268362e479461eb221c1d97ee7d776be6bd175f9` |
| Capture SHA-256 | `b4a7435673024c59ca3cc414829d5999682cf4af41a7499caacc97d6f5a95b56` | `9d91dccf698c483c4a944eb5dcbd0eed9556198fa1de18c4e7e382602a314057` |
| Result | 442 motion records, `MOUSE session-end records=442`, `WIFI-END status=0` | 560 records, `WIFI-END status=0`, including the left, right and middle buttons (`buttons=1`, `2`, `4`) pressed one at a time on request |

**The diagnostic trace.** It printed each transfer event and, every 2 s, the controller, slot and endpoint state. Two changes came with it: the endpoint context's Average TRB Length set to the max packet size, and the trace prints. The unchanged program's capture shows that neither is needed.

**No wheel, as expected.** In boot protocol this mouse sends 3-byte reports (buttons, X, Y), as HID 1.11 Appendix B.2 defines them. The trace shows every completion as Short Packet with residual 1, so the program prints `wheel=0`. QEMU's `usb-mouse` sends a fourth, wheel byte even in boot protocol, which is why the QEMU scenario sees wheel motion. Real mice report the wheel only in report protocol.

**A method note.** Earlier sessions of the same programs, behind the hub, recorded only one or two small start-up reports. In those sessions nobody had moved the mouse yet: the prompt to start reached the person late. They are not evidence of a fault and are not kept here. The two captures above were taken with the person confirmed at the mouse.

## Not established here

- Mouse motion through the hub's TT. The mouse's start-up reports did arrive through it, and the keyboard's typing session used the same TT path.
- Num Lock and Scroll Lock on hardware. They are checked in simulation (`leanos-usb-kbd-decode`); only Caps Lock was pressed here.
