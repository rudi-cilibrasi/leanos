#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/hosted-sanitizer-config.sh
leanos_assert_pinned_toolchain
build=build/qotom-native-fields
# The preceding scalar object check built retained.o without Lean dependencies.
test -f "$build/retained.o"
python3 - "$build/capture.h" <<'PY'
import hashlib
import json
from pathlib import Path
import sys
capture = Path('hardware/lab/observations/qotom-ecam-20260911')
name = 'cycle-1/reclassified-result.json'
raw = (capture / name).read_bytes()
manifest = json.loads((capture / 'manifest.json').read_text())
if hashlib.sha256(raw).hexdigest() != manifest['files'][name]:
    raise SystemExit('native capture hash mismatch')
rows = json.loads(raw)['diagnostic']['pci_headers']
if len(rows) != 16 or any(len(row) != 19 for row in rows):
    raise SystemExit('bad fixture dimensions')
lines = ['static const struct pci_enumeration_snapshot captured = {16, {']
for row in rows:
    lines.append('{' + ','.join(str(x) for x in row[:3]) + ',{' +
                 ','.join(hex(x) for x in row[3:]) + '}},')
lines.append('}};')
Path(sys.argv[1]).write_text('\n'.join(lines) + '\n')
PY
"$leanos_host_cc" -O2 -Wall -Wextra -Werror -I"$build" -Ibuild/boundary-abi \
  tests/qotom-native-snapshot-sanitizers.c "$build/retained.o" -o "$build/snapshot-ordinary"
"$build/snapshot-ordinary" > "$build/snapshot-ordinary.log"
"$leanos_host_cc" "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror -I"$build" -Ibuild/boundary-abi \
  -c tests/qotom-native-snapshot-sanitizers.c -o "$build/snapshot-sanitized.o"
leanos_require_sanitized_object "$build/snapshot-sanitized.o"
"$leanos_host_cc" "${leanos_host_sanitizer_flags[@]}" \
  "$build/snapshot-sanitized.o" "$build/retained.o" -o "$build/snapshot-sanitized"
leanos_run_sanitized "$build/snapshot-sanitized" > "$build/snapshot-sanitized.log"
cmp "$build/snapshot-ordinary.log" "$build/snapshot-sanitized.log"
cat "$build/snapshot-sanitized.log"
# Negative control: the same harness must detect a seventeenth header read.
python3 - "$build/overrun.h" <<'PY'
from pathlib import Path
import sys
source = Path('boot/qotom-native-inventory.h').read_text()
needle = 'i < 16; ++i'
if source.count(needle) != 1:
    raise SystemExit('snapshot overrun mutation no longer has exactly one target')
Path(sys.argv[1]).write_text(source.replace(needle, 'i < 17; ++i'))
PY
"$leanos_host_cc" "${leanos_host_sanitizer_flags[@]}" -Wall -Wextra -Werror \
  -Iboot -I"$build" -Ibuild/boundary-abi -include "$build/overrun.h" \
  tests/qotom-native-snapshot-sanitizers.c "$build/retained.o" -o "$build/snapshot-overrun"
ulimit -c 0
if leanos_run_sanitized "$build/snapshot-overrun" > "$build/snapshot-overrun.log" 2>&1; then
  echo 'sanitizer failed to reject the seventeenth-header mutation' >&2
  exit 1
fi
if ! grep -Fq 'AddressSanitizer: stack-buffer-overflow' "$build/snapshot-overrun.log" ||
   ! grep -Fq 'qotom_check_native_inventory' "$build/snapshot-overrun.log"; then
  echo 'overrun control failed without a sanitizer diagnostic' >&2
  cat "$build/snapshot-overrun.log" >&2
  exit 1
fi
printf '%s\n' 'PASS sanitizer rejects seventeenth-header mutation'
