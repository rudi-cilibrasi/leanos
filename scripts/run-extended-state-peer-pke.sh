#!/usr/bin/env bash
set -euo pipefail
serial_protocol="${LEANOS_SERIAL_PROTOCOL:-$(dirname "${LEANOS_ORACLE_CORPUS:-build/boot/corpus.tsv}")/serial-protocol.sh}"
# shellcheck source=/dev/null
source "$serial_protocol"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
source "$repo_root/scripts/q35-platform.sh"
qemu="${LEANOS_QEMU:-qemu-system-x86_64}"
limit="${LEANOS_QEMU_TIMEOUT_SECONDS:-30}"
version="${LEANOS_VERSION:-0.1.0}"
image="${1:-${LEANOS_BOOT_DIR:-build/boot}/leanos-${version}-x86_64-extended-state-peer-pke.iso}"
log="${LEANOS_SERIAL_LOG:-build/boot/extended-state-peer-pke.serial.log}"

for tool in "$qemu" timeout; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "error: missing required tool '$tool'" >&2
    exit 1
  }
done
[[ "$limit" =~ ^[1-9][0-9]*$ ]] || { echo "error: invalid timeout" >&2; exit 1; }
[[ -f "$image" ]] || { echo "error: missing peer-control image '$image'" >&2; exit 1; }
mkdir -p "$(dirname "$log")"
: > "$log"
command=()
leanos_q35_command command "$qemu" 128 "$log" "$image"
qemu_version="$($qemu --version 2>&1 | head -n 1 || true)"
printf 'QEMU version: %s\nQEMU command:' "${qemu_version:-unknown}" >&2
printf ' %q' "${command[@]}" >&2
printf '\nSerial log: %s\n' "$log" >&2
set +e
timeout --signal=TERM --kill-after=2s "${limit}s" "${command[@]}"
status=$?
set -e
[[ $status -ne 124 && $status -ne 137 ]] || {
  echo "error: peer-control image timed out" >&2; exit 1;
}
[[ $status -eq 35 ]] || {
  echo "error: peer-control image exited $status instead of typed guest failure 35" >&2
  exit 1
}
failure="${LEANOS_SERIAL_3_FINAL} status=FAIL reason=extended-state-denial-peer-controls"
[[ $(grep -Fxc "$failure" "$log") -eq 1 ]] || {
  echo "error: peer-control image lacked its exact control-denial result" >&2
  exit 1
}
grep -Fq "${LEANOS_SERIAL_13_EXTENDED_STATE} event=deny subject=1" "$log" || {
  echo "error: peer-control image did not reach authoritative peer dispatch" >&2
  exit 1
}
mapfile -t injected < <(
  grep "^${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer-control-injected " "$log" || true
)
[[ ${#injected[@]} -eq 1 ]] || {
  echo "error: peer-control image lacked one exact live-control witness" >&2
  exit 1
}
pke="${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer-control-injected control=pke bit=22 live=1 stage=pre-iretq result=PASS"
osxsave="${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer-control-injected control=osxsave bit=18 live=1 stage=pre-iretq result=PASS"
accelerator="$(leanos_qemu_accelerator)"
if [[ "$accelerator" == tcg ]]; then
  [[ "${injected[0]}" == "$pke" ]] || {
    echo "error: pinned TCG peer-control image did not exercise PKE" >&2
    exit 1
  }
elif [[ "${injected[0]}" != "$pke" && "${injected[0]}" != "$osxsave" ]]; then
  echo "error: KVM peer-control image reported an unreviewed control" >&2
  exit 1
fi
if grep -Eq "^${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer-cpl3-entry|^${LEANOS_SERIAL_13_EXTENDED_STATE} event=peer |^${LEANOS_SERIAL_13_FINAL} status=PASS" "$log"; then
  echo "error: peer-control image entered CPL3 or published success after a forbidden control" >&2
  exit 1
fi
echo "Extended-state peer-return forbidden-control rejection passed"
