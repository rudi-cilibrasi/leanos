#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/multivcpu-rejection.serial.log}"
qmp_log="${LEANOS_QMP_LOG:-${log}.qmp.jsonl}"
inventory="${LEANOS_MULTIVCPU_INVENTORY:-${log}.qmp.tsv}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
terminal='LEANOS/7 BOOTALLOC status=FAIL reason=topology-madt-generated-entries'

for tool in "$qemu" timeout python3; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || {
  echo "error: timeout must be a positive integer" >&2
  exit 1
}
[[ "$memory_mib" =~ ^(64|128)$ ]] || {
  echo "error: memory must be 64 or 128 MiB" >&2
  exit 1
}
[[ -f "$image" ]] || {
  echo "error: image '$image' not found; run ./scripts/build-image.sh first" >&2
  exit 1
}

mkdir -p "$(dirname "$log")" "$(dirname "$qmp_log")" "$(dirname "$inventory")"
: > "$log"
: > "$qmp_log"
socket_root="$(mktemp -d "${TMPDIR:-/tmp}/leanos-mvcpu.XXXXXX")"
monitor="$socket_root/qmp.sock"
command=()
leanos_q35_command command "$qemu" "$memory_mib" "$log" "$image" max \
  '2,sockets=1,cores=2,threads=1'
command+=(-qmp "unix:${monitor},server=on,wait=off")

qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
printf ' %q' "${command[@]}" >&2
printf '\nSerial log: %s\nQMP transcript: %s\n' "$log" "$qmp_log" >&2

set +e
timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}" &
qemu_job=$!
set -e
cleanup() {
  kill "$qemu_job" 2>/dev/null || true
  rm -rf "$socket_root"
}
trap cleanup EXIT

socket_seen=0
for _ in $(seq 1 200); do
  if [[ -S "$monitor" ]]; then socket_seen=1; break; fi
  kill -0 "$qemu_job" 2>/dev/null || break
  sleep 0.01
done
[[ "$socket_seen" -eq 1 ]] || {
  echo "failure_class=qmp-startup: QMP socket was not available before guest exit" >&2
  exit 1
}

python3 - "$monitor" "$qmp_log" <<'PY'
import json
import socket
import sys

with open(sys.argv[2], "w", encoding="utf-8") as transcript:
    def record(direction, message):
        transcript.write(json.dumps(
            {"direction": direction, "message": message}, sort_keys=True
        ) + "\n")
        transcript.flush()

    def receive(stream):
        line = stream.readline()
        if not line:
            raise RuntimeError("QMP connection closed before reply")
        message = json.loads(line)
        record("qemu-to-host", message)
        return message

    def send(stream, message):
        record("host-to-qemu", message)
        stream.write(json.dumps(message, separators=(",", ":")).encode() + b"\n")

    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
        client.settimeout(2)
        client.connect(sys.argv[1])
        stream = client.makefile("rwb", buffering=0)
        if "QMP" not in receive(stream):
            raise RuntimeError("missing QMP greeting")
        send(stream, {"execute": "qmp_capabilities"})
        if "return" not in receive(stream):
            raise RuntimeError("QMP capabilities rejected")
        send(stream, {"execute": "query-cpus-fast"})
        if "return" not in receive(stream):
            raise RuntimeError("QMP CPU inventory rejected")
PY
python3 scripts/check-multivcpu-qmp.py "$qmp_log" "$inventory"

set +e
wait "$qemu_job"
status=$?
set -e
trap - EXIT
rm -rf "$socket_root"

if [[ $status -eq 124 || $status -eq 137 ]]; then
  echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2
  exit 1
fi
if [[ $status -ne 35 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 35)" >&2
  exit 1
fi
if [[ "$(grep -Fxc "$terminal" "$log")" -ne 1 ]]; then
  echo "failure_class=terminal-record: exact topology rejection not observed" >&2
  exit 1
fi
if awk -v terminal="$terminal" '
  seen { extra=1 }
  $0 == terminal { seen=1 }
  END { exit !(seen && !extra) }
' "$log"; then
  :
else
  echo "failure_class=post-terminal-output: rejection was not the final record" >&2
  exit 1
fi
if grep -Eqi '^LEANOS/[0-9]+ (CPL3|ENTRY|TIMER|CONTEXT|SWITCH|SYSCALL|PEER|TLB-CPL3|FINAL)([[:space:]]|$)|(^|[[:space:]])(enter_user|user-return|scheduler-dispatch|timer-armed)=' "$log"; then
  echo "failure_class=authority-leak: rejected topology reached runtime authority" >&2
  exit 1
fi

echo "LeanOS multi-vCPU rejection passed; exact QMP topology and pre-CPL3 terminal retained"
