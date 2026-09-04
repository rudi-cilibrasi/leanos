#!/usr/bin/env bash
# Capture the firmware handoff inputs of a Linux guest booted under QEMU for
# the firmware handoff corpus (docs/firmware-handoff-corpus.md). The guest
# runs the same capture procedure as a physical machine
# (scripts/capture-firmware-handoff.sh) from a minimal initramfs, so a
# firmware family that QEMU ships (SeaBIOS) or loads from a file (OVMF) can
# contribute a corpus row with the same provenance shape as a live capture.
# The harness builds the initramfs itself (busybox, bash and its libraries,
# and the capture script), boots the given kernel with the chosen firmware,
# reads the capture back over the serial console, and records the guest
# construction in the capture's provenance. Nothing here touches the captured
# bytes: the capture script hashes what it wrote, and this script only adds
# the `guest` provenance object beside those hashes.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

usage() {
  cat >&2 <<'EOF'
usage: scripts/capture-firmware-handoff-qemu.sh --kernel <bzImage> --busybox <static-busybox>
         --firmware seabios|ovmf [--ovmf-code <fd> --ovmf-vars <fd>]
         [--cpus N] [--memory MiB] [--timeout SECONDS]
         [--kernel-package <text>] [--busybox-package <text>] [--ovmf-package <text>]
         <capture-directory>
EOF
  exit 2
}

kernel="" busybox="" firmware="" ovmf_code="" ovmf_vars=""
cpus=1 memory=1024 limit=300
kernel_package="" busybox_package="" ovmf_package=""
out=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --kernel) kernel="$2"; shift 2 ;;
    --busybox) busybox="$2"; shift 2 ;;
    --firmware) firmware="$2"; shift 2 ;;
    --ovmf-code) ovmf_code="$2"; shift 2 ;;
    --ovmf-vars) ovmf_vars="$2"; shift 2 ;;
    --cpus) cpus="$2"; shift 2 ;;
    --memory) memory="$2"; shift 2 ;;
    --timeout) limit="$2"; shift 2 ;;
    --kernel-package) kernel_package="$2"; shift 2 ;;
    --busybox-package) busybox_package="$2"; shift 2 ;;
    --ovmf-package) ovmf_package="$2"; shift 2 ;;
    -*) usage ;;
    *) [[ -z "$out" ]] || usage; out="$1"; shift ;;
  esac
done
[[ -n "$kernel" && -n "$busybox" && -n "$firmware" && -n "$out" ]] || usage
[[ "$cpus" =~ ^[1-9][0-9]*$ && "$memory" =~ ^[1-9][0-9]*$ && "$limit" =~ ^[1-9][0-9]*$ ]] || usage
case "$firmware" in
  seabios) ;;
  ovmf) [[ -n "$ovmf_code" && -n "$ovmf_vars" ]] || usage ;;
  *) usage ;;
esac
for path in "$kernel" "$busybox" ${ovmf_code:+"$ovmf_code"} ${ovmf_vars:+"$ovmf_vars"}; do
  [[ -f "$path" ]] || { echo "error: $path is not a file" >&2; exit 1; }
done
[[ -e "$out" ]] && { echo "error: $out already exists" >&2; exit 1; }
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
for tool in "$qemu" timeout python3 gzip; do
  command -v "$tool" >/dev/null 2>&1 || { echo "error: missing required tool '$tool'" >&2; exit 1; }
done

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
sha() { sha256sum "$1" | cut -d ' ' -f 1; }

# Stage the initramfs: busybox provides the shell and the coreutils the
# capture script needs, bash runs the script itself, and /init drives the
# capture and streams it back over the serial console.
stage="$work/initramfs"
mkdir -p "$stage/bin" "$stage/dev" "$stage/proc" "$stage/sys" "$stage/tmp" \
  "$stage/capture" "$stage/lib/x86_64-linux-gnu" "$stage/lib64" "$stage/scripts"
cp "$busybox" "$stage/bin/busybox"
chmod 755 "$stage/bin/busybox"
while IFS= read -r applet; do
  [[ "$applet" == busybox ]] && continue
  ln -s busybox "$stage/bin/$applet"
done < <("$busybox" --list)
cp /bin/bash "$stage/bin/bash"
while IFS= read -r library; do
  case "$library" in
    */ld-linux-x86-64.so.2) cp "$library" "$stage/lib64/ld-linux-x86-64.so.2" ;;
    /*) cp "$library" "$stage/lib/x86_64-linux-gnu/$(basename "$library")" ;;
  esac
done < <(ldd /bin/bash | awk '{ for (i = 1; i <= NF; i++) if ($i ~ /^\//) { print $i; break } }')
cp scripts/capture-firmware-handoff.sh "$stage/scripts/capture-firmware-handoff.sh"
chmod 755 "$stage/scripts/capture-firmware-handoff.sh"
cat > "$stage/init" <<'EOF'
#!/bin/sh
export PATH=/bin
mount -t proc proc /proc
mount -t sysfs sysfs /sys
mount -t devtmpfs devtmpfs /dev
exec > /dev/ttyS0 2>&1
if /bin/bash /scripts/capture-firmware-handoff.sh /capture/handoff; then
  echo LEANOS-CAPTURE-BEGIN
  tar cf - -C /capture/handoff . | base64
  echo LEANOS-CAPTURE-END
else
  echo LEANOS-CAPTURE-FAILED
fi
poweroff -f
echo o > /proc/sysrq-trigger
sleep 30
EOF
chmod 755 "$stage/init"

# cpio(1) is not part of the pinned tool inventory, so write the newc archive
# directly: one deterministic entry per staged path, zero mtimes, and the
# console and serial device nodes the kernel needs before devtmpfs is mounted.
python3 - "$stage" "$work/initramfs.cpio" <<'EOF'
import os
import stat
import sys

stage, archive = sys.argv[1], sys.argv[2]


def pad4(data: bytes) -> bytes:
    return data + b"\0" * (-len(data) % 4)


def entry(ino: int, name: str, mode: int, data: bytes, rdev=(0, 0)) -> bytes:
    encoded = name.encode() + b"\0"
    header = "070701" + "".join(
        f"{value:08x}" for value in (
            ino, mode, 0, 0, 1, 0, len(data), 0, 0, rdev[0], rdev[1], len(encoded), 0
        )
    )
    return pad4(header.encode() + encoded) + pad4(data)


entries = []
ino = 1
for directory, names, files in os.walk(stage):
    relative = os.path.relpath(directory, stage)
    if relative != ".":
        entries.append((relative, stat.S_IFDIR | 0o755, b"", (0, 0)))
    for name in sorted(names + files):
        path = os.path.join(directory, name)
        rel = os.path.normpath(os.path.join(relative, name))
        info = os.lstat(path)
        if stat.S_ISLNK(info.st_mode):
            entries.append((rel, stat.S_IFLNK | 0o777, os.readlink(path).encode(), (0, 0)))
        elif stat.S_ISREG(info.st_mode):
            mode = 0o755 if info.st_mode & stat.S_IXUSR else 0o644
            with open(path, "rb") as handle:
                entries.append((rel, stat.S_IFREG | mode, handle.read(), (0, 0)))
    names[:] = sorted(names)
entries.append(("dev/console", stat.S_IFCHR | 0o600, b"", (5, 1)))
entries.append(("dev/ttyS0", stat.S_IFCHR | 0o600, b"", (4, 64)))
entries.sort(key=lambda item: item[0])
with open(archive, "wb") as handle:
    for name, mode, data, rdev in entries:
        handle.write(entry(ino, name, mode, data, rdev))
        ino += 1
    handle.write(entry(ino, "TRAILER!!!", 0, b""))
EOF
gzip -9 -n "$work/initramfs.cpio"

# Boot the guest with the chosen firmware. The serial console is the only
# channel: the kernel logs there, the capture is streamed there in base64
# between two markers, and the guest powers itself off afterwards.
log="$work/serial.log"
command=("$qemu" -machine q35 -smp "$cpus" -m "$memory" -display none -monitor none
  -no-reboot -serial "file:$log" -kernel "$kernel" -initrd "$work/initramfs.cpio.gz"
  -append "console=ttyS0 rdinit=/init loglevel=4 panic=-1")
if [[ "$firmware" == ovmf ]]; then
  cp "$ovmf_vars" "$work/OVMF_VARS.fd"
  command+=(-drive "if=pflash,format=raw,readonly=on,file=$ovmf_code"
    -drive "if=pflash,format=raw,file=$work/OVMF_VARS.fd")
fi
printf '%q ' timeout "$limit" "${command[@]}" >&2
echo >&2
set +e
timeout "$limit" "${command[@]}"
status=$?
set -e
if [[ $status -eq 124 ]]; then
  echo "error: the guest did not finish within ${limit}s; serial log: $log" >&2
  cp "$log" "${out}.serial.log"
  exit 1
fi
if ! grep -q '^LEANOS-CAPTURE-END' "$log"; then
  echo "error: the guest emitted no complete capture (QEMU status $status); serial log kept at ${out}.serial.log" >&2
  cp "$log" "${out}.serial.log"
  exit 1
fi

# Unpack the capture exactly as the guest wrote it, then add the guest
# construction to its provenance beside the hashes the capture script recorded.
mkdir -p "$out"
python3 - "$log" "$out" <<'EOF'
import base64
import io
import sys
import tarfile

log, out = sys.argv[1], sys.argv[2]
lines = open(log, "rb").read().replace(b"\r", b"").split(b"\n")
begin = lines.index(b"LEANOS-CAPTURE-BEGIN")
end = lines.index(b"LEANOS-CAPTURE-END", begin)
payload = base64.b64decode(b"".join(lines[begin + 1:end]), validate=True)
with tarfile.open(fileobj=io.BytesIO(payload), mode="r:") as archive:
    for member in archive.getmembers():
        if not (member.isfile() or member.isdir()) or member.name.startswith(("/", "..")):
            raise SystemExit(f"error: unexpected archive member {member.name!r}")
    archive.extractall(out, filter="data")
EOF
for required in memmap.tsv acpi/APIC.bin executing-apic-id.txt provenance.json; do
  [[ -s "$out/$required" ]] || { echo "error: capture lacks $required" >&2; exit 1; }
done
emulator="$("$qemu" --version | head -n 1)"
python3 - "$out/provenance.json" "$emulator" "$firmware" "$cpus" "$memory" \
  "$kernel_package" "$(sha "$kernel")" "$busybox_package" "$(sha "$busybox")" \
  "$ovmf_package" "${ovmf_code:+$(sha "$ovmf_code")}" <<'EOF'
import json
import sys

(path, emulator, firmware, cpus, memory, kernel_package, kernel_sha, busybox_package,
 busybox_sha, ovmf_package, ovmf_sha) = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    provenance = json.load(handle)
guest = {
    "emulator": emulator,
    "machine": "q35",
    "firmware": firmware,
    "cpus": int(cpus),
    "memory_mib": int(memory),
    "kernel_package": kernel_package,
    "kernel_sha256": kernel_sha,
    "busybox_package": busybox_package,
    "busybox_sha256": busybox_sha,
}
if firmware == "ovmf":
    guest["ovmf_package"] = ovmf_package
    guest["ovmf_code_sha256"] = ovmf_sha
provenance["guest"] = guest
with open(path, "w", encoding="utf-8") as handle:
    json.dump(provenance, handle, indent=2)
    handle.write("\n")
EOF
cp "$log" "${out}.serial.log"
echo "captured $firmware guest firmware handoff inputs into $out (serial log: ${out}.serial.log)"
