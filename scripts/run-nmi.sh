#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-build/boot/leanos-${version}-x86_64-nmi.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/nmi.serial.log}"
qmp_log="${LEANOS_QMP_LOG:-${log}.qmp.jsonl}"
memory_mib="${LEANOS_QEMU_MEMORY_MIB:-128}"
monitor="${log}.monitor"
ready='LEANOS/17 NMI-READY origin=cpl0 prior=handling if=0 gate=2 ist=2 result=PASS'
terminal='LEANOS/17 NMI reason=non-maskable-interrupt vector=2 error=none ist=2 frame=rip,cs,rflags,rsp,ss origin=cpl0 prior=handling terminal=latched return=none'

for tool in "$qemu" timeout python3; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: timeout must be positive" >&2; exit 1; }
[[ "$memory_mib" =~ ^(64|128)$ ]] || { echo "error: memory must be 64 or 128 MiB" >&2; exit 1; }
[[ -f "$image" ]] || { echo "error: NMI image '$image' not found" >&2; exit 1; }

mkdir -p "$(dirname "$log")"
: > "$log"
: > "$qmp_log"
rm -f "$monitor"
command=("$qemu" -machine q35,accel=tcg -cpu max -smp 1
  -m "${memory_mib}M" -display none
  -monitor none -qmp "unix:${monitor},server=on,wait=off" -serial "file:$log"
  -no-reboot -no-shutdown -nic none
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 -cdrom "$image")
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
printf ' %q' "${command[@]}" >&2
printf '\nSerial log: %s\n' "$log" >&2
printf 'QMP transcript: %s\n' "$qmp_log" >&2

set +e
timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}" &
qemu_job=$!
set -e
cleanup() { rm -f "$monitor"; kill "$qemu_job" 2>/dev/null || true; }
trap cleanup EXIT

ready_seen=0
for _ in $(seq 1 600); do
  if grep -Fqx "$ready" "$log" && [[ -S "$monitor" ]]; then
    ready_seen=1
    break
  fi
  kill -0 "$qemu_job" 2>/dev/null || break
  sleep 0.05
done
if [[ "$ready_seen" -ne 1 ]]; then
  echo "failure_class=nmi-ready: guest did not publish the injection boundary" >&2
  exit 1
fi
if grep -q '^LEANOS/17 NMI reason=' "$log"; then
  echo "failure_class=injection-boundary: terminal record preceded host injection" >&2
  exit 1
fi

set +e
python3 - "$monitor" "$qmp_log" <<'PY'
import json
import socket
import sys

transcript = open(sys.argv[2], "w", encoding="utf-8")

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
    greeting = receive(stream)
    if "QMP" not in greeting:
        raise RuntimeError("missing QMP greeting")
    send(stream, {"execute": "qmp_capabilities"})
    if "return" not in receive(stream):
        raise RuntimeError("QMP capabilities rejected")
    send(stream, {"execute": "inject-nmi"})
    if "return" not in receive(stream):
        raise RuntimeError("QMP NMI injection rejected")
transcript.close()
PY
qmp_status=$?
set -e
if [[ "$qmp_status" -ne 0 ]]; then
  echo "failure_class=qmp-injection: inject-nmi command did not complete" >&2
  exit 1
fi

set +e
wait "$qemu_job"
status=$?
set -e
trap - EXIT
rm -f "$monitor"

if [[ $status -eq 124 || $status -eq 137 ]]; then
  echo "failure_class=timeout: QEMU exceeded ${limit}s wall limit" >&2
  exit 1
fi
if [[ $status -eq 43 ]]; then
  echo "failure_class=guest-evidence: guest rejected the NMI frame or IST2 state" >&2
  exit 1
fi
if [[ $status -ne 41 ]]; then
  echo "failure_class=qemu-error: QEMU exit status $status (expected 41)" >&2
  exit 1
fi
if [[ "$(grep -Fxc "$ready" "$log")" -ne 1 || \
      "$(grep -Fxc "$terminal" "$log")" -ne 1 ]]; then
  echo "failure_class=terminal-record: exact ready and terminal records not observed" >&2
  exit 1
fi
if [[ "$(grep -c '^LEANOS/17 NMI reason=' "$log")" -ne 1 ]] || \
   grep -Eq '^LEANOS/17 NMI status=FAIL|terminal=.*return=(iretq|resumed)|LEANOS/[0-9]+ FINAL ' "$log"; then
  echo "failure_class=terminal-record: forged, failed, duplicate, or post-terminal output observed" >&2
  exit 1
fi
python3 - "$qmp_log" <<'PY'
import json
import sys

records = [json.loads(line) for line in open(sys.argv[1], encoding="utf-8")]
commands = [record["message"].get("execute") for record in records
            if record["direction"] == "host-to-qemu"]
if commands != ["qmp_capabilities", "inject-nmi"] or len(records) != 5:
    raise SystemExit("failure_class=qmp-transcript: exact injection exchange not retained")
PY

echo "LeanOS NMI probe passed; retained QMP injection crossed IF=0 onto IST2 and latched the terminal handler"
