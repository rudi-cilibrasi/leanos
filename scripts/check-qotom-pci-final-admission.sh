#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
build=build/qotom-pci-final
mkdir -p "$build"
scripts/build-qotom-native-pci-object.sh "$build/native-pci"
python3 - "$build/capture.h" <<'PY'
import hashlib,json,sys
from pathlib import Path
capture=Path('hardware/lab/observations/qotom-ecam-20260911')
name='cycle-1/reclassified-result.json'
raw=(capture/name).read_bytes();manifest=json.loads((capture/'manifest.json').read_text())
if hashlib.sha256(raw).hexdigest()!=manifest['files'][name]:raise SystemExit('capture hash')
rows=json.loads(raw)['diagnostic']['pci_headers']
if len(rows)!=16 or any(len(row)!=19 for row in rows):raise SystemExit('capture shape')
lines=['static const struct pci_enumeration_snapshot captured = {16, {']
for row in rows:
    lines.append('{'+','.join(str(x) for x in row[:3])+',{' +
        ','.join(hex(x) for x in row[3:])+'}},')
lines.append('}};')
Path(sys.argv[1]).write_text('\n'.join(lines)+'\n')
PY
"${CC:-gcc}" -no-pie -std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-function -Iboot -I"$build" \
  -Ibuild/boundary-abi tests/qotom-pci-final-admission.c \
  "$build/native-pci/native-pci.o" -o "$build/test"
"$build/test"
"${CC:-gcc}" -no-pie -std=c11 -O2 -Wall -Wextra -Werror \
  -Ibuild/boundary-abi tests/qotom-nosmap-control.c \
  "$build/native-pci/native-pci.o" -o "$build/nosmap-control-test"
"$build/nosmap-control-test"
"${CC:-gcc}" -no-pie -std=c11 -O2 -Wall -Wextra -Werror \
  -Ibuild/boundary-abi tests/qotom-copy-root-publication.c \
  "$build/native-pci/native-pci.o" -o "$build/copy-root-publication-test"
"$build/copy-root-publication-test"
"${CC:-gcc}" -no-pie -std=c11 -O2 -Wall -Wextra -Werror \
  -Iinclude tests/qotom-copy-root-builder.c -o "$build/copy-root-builder-test"
"$build/copy-root-builder-test"
