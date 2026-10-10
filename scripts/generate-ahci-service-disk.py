#!/usr/bin/env python3
"""Generate the fixed disk image of the ahci-service scenario (issue #496).

The q35 `ahci-service` construction attaches this image behind port 1 of the
built-in ICH9 AHCI; the Lean one-sector program (`LeanOS.Storage.AhciRead`)
reads the sector at its fixed LBA and the kernel hands its 128 dwords to a
ring-3 subject over IPC. The image is generated, not committed: it is a pure
function of this file, so every run reads the same bytes.

Each of the 16 sectors starts with a 32-byte ASCII label naming its LBA,
so reading the wrong sector is visible, followed by 120 dwords from a
multiplicative pattern seeded by the LBA. Every 16th dword is zero, so the
service's sequence framing (a zero dword is not end-of-stream) is exercised.

usage:
  generate-ahci-service-disk.py --output IMAGE
  generate-ahci-service-disk.py --words LBA     # the sector's dwords, one per line
  generate-ahci-service-disk.py --digest LBA    # FNV-1a (32-bit) of the sector
  generate-ahci-service-disk.py --check-transcript TRANSCRIPT [--lean FILE]
"""

from __future__ import annotations

import argparse
import re
import struct
import sys
from pathlib import Path

SECTOR_BYTES = 512
SECTORS = 16
ROOT = Path(__file__).resolve().parent.parent


def sector(lba: int) -> bytes:
    if not 0 <= lba < SECTORS:
        raise ValueError(f"LBA {lba} is outside the {SECTORS}-sector image")
    label = f"LeanOS ahci-service LBA {lba:02d}".encode("ascii").ljust(32, b" ")
    words = []
    for k in range(8, SECTOR_BYTES // 4):
        words.append(0 if k % 16 == 0 else ((lba + 1) * 0x9E3779B1 * (k + 1)) & 0xFFFFFFFF)
    return label + struct.pack("<120I", *words)


def image() -> bytes:
    return b"".join(sector(lba) for lba in range(SECTORS))


def words(lba: int) -> list[int]:
    return list(struct.unpack("<128I", sector(lba)))


def fnv1a(data: bytes) -> int:
    value = 0x811C9DC5
    for byte in data:
        value = ((value ^ byte) * 16777619) & 0xFFFFFFFF
    return value


def lean_lba(path: Path) -> int:
    match = re.search(r"^def readLba : UInt32 := (\d+)$", path.read_text(encoding="utf-8"), re.M)
    if match is None:
        raise ValueError(f"{path} does not define readLba")
    return int(match.group(1))


def check_transcript(transcript: Path, lean: Path) -> None:
    """The committed transcript must carry exactly the generated sector at the
    program's LBA: its read record, one send per dword with its sequence
    number, and the digest in the final record."""
    lba = lean_lba(lean)
    expected = words(lba)
    text = transcript.read_text(encoding="utf-8")
    reads = re.findall(r"^@10/DEVICE@ event=read subject=1 device=0:31\.2 port=1 lba=(\d+) ",
                       text, re.M)
    if reads != [str(lba)]:
        raise ValueError(f"transcript read record names {reads}, not LBA {lba}")
    sends = [(int(a), int(b)) for a, b in re.findall(
        r"^@10/IPC@ event=send sender=1 endpoint=10 payload0=(\d+) payload1=(\d+) accepted=1$",
        text, re.M)]
    if sends != [(word, index + 1) for index, word in enumerate(expected)]:
        raise ValueError("transcript payloads are not the generated sector in order")
    digests = re.findall(r"^@10/FINAL@ status=PASS .* sector-fnv1a=(\d+) ", text, re.M)
    if digests != [str(fnv1a(sector(lba)))]:
        raise ValueError(f"transcript digest {digests} disagrees with the generated sector")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--output", type=Path)
    group.add_argument("--words", type=int, metavar="LBA")
    group.add_argument("--digest", type=int, metavar="LBA")
    group.add_argument("--check-transcript", type=Path, metavar="TRANSCRIPT")
    parser.add_argument("--lean", type=Path, default=ROOT / "LeanOS/Storage/AhciRead.lean")
    args = parser.parse_args()
    try:
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(image())
        elif args.words is not None:
            print("\n".join(str(word) for word in words(args.words)))
        elif args.digest is not None:
            print(fnv1a(sector(args.digest)))
        else:
            check_transcript(args.check_transcript, args.lean)
            print(f"ahci-service transcript carries the generated sector: {args.check_transcript}")
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
