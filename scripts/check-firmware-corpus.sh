#!/usr/bin/env bash
# Firmware handoff corpus gate (docs/firmware-handoff-corpus.md): the manifest
# validates, conversion is deterministic and matches the recorded digests, the
# Lean definitions return every pinned word for every case and mutation, and
# the validator rejects each kind of corpus drift with a case-local diagnostic.
# The generated-C side of the same inputs runs as the `firmware-corpus` hosted
# boundary.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tool=./scripts/firmware-corpus.py
out=build/firmware-corpus
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

python3 "$tool" validate
rm -rf "$out"
python3 "$tool" normalize --out "$out"
python3 "$tool" normalize --out "$tmp/again" > /dev/null
for file in $(cd "$out" && find . -type f -name '*.bin' | sort); do
  cmp -s "$out/$file" "$tmp/again/$file" || {
    echo "error: firmware corpus conversion is not deterministic: $file" >&2
    exit 1
  }
done
cases="$(python3 "$tool" list | wc -l)"
rows="$(grep -c -v '^#' "$out/replay.tsv")"
(( cases >= 3 )) || { echo "error: the corpus must hold at least three firmware captures" >&2; exit 1; }
(( rows == cases * 16 )) || { echo "error: expected $((cases * 16)) replay rows, found $rows" >&2; exit 1; }
python3 "$tool" list | awk -F '\t' '
  $3 == "accepted" { handoff++ }
  $4 == "accepted" { admitted++ }
  $4 ~ /^admission-rejected:multipleEnabledProcessors$/ { rejected++ }
  END {
    if (handoff < 1 || admitted < 1 || rejected < 1) {
      print "error: the corpus must include a decoded memory map, an admitted topology, and a rejected multi-processor topology" > "/dev/stderr"
      exit 1
    }
  }'

# Lean evaluation of the same bytes against the same words.
lean_log="$tmp/corpus-lean.log"
if ! lake env lean "$out/Corpus.lean" > "$lean_log" 2>&1; then
  cat "$lean_log" >&2
  echo "error: the Lean definitions disagree with the corpus manifest" >&2
  exit 1
fi

# Validator negatives: each mutation of the checked corpus fails with the
# named diagnostic. Every fixture works on a private copy.
expect_rejection() {
  local name="$1" expected="$2" script="$3"
  local copy="$tmp/$name"
  rm -rf "$copy"
  cp -r firmware-corpus "$copy"
  python3 - "$copy" <<PY
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
manifest = json.loads((root / "manifest.json").read_text())
case = manifest["cases"][0]
$script
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
PY
  local output
  if output="$(python3 "$tool" --manifest "$copy/manifest.json" validate 2>&1)"; then
    echo "error: corpus fixture $name was accepted" >&2
    exit 1
  fi
  [[ "$output" == *"$expected"* ]] || {
    echo "error: corpus fixture $name failed for the wrong reason: $output" >&2
    exit 1
  }
}
expect_rejection duplicate-id "duplicate case id" \
  'manifest["cases"].append(dict(case))'
expect_rejection tampered-input "does not match its recorded sha256" \
  '(root / case["id"] / "memmap.tsv").write_text((root / case["id"] / "memmap.tsv").read_text() + "5\t0x0\t0xfff\tSystem RAM\n")'
expect_rejection forged-digest "does not match its recorded sha256" \
  'case["inputs"]["acpi/APIC.bin"] = "0" * 64'
expect_rejection missing-input "input executing-apic-id.txt is missing" \
  '(root / case["id"] / "executing-apic-id.txt").unlink()'
expect_rejection provenance-drift "capture provenance records a different memmap.tsv" \
  'p = root / case["id"] / "provenance.json"; d = json.loads(p.read_text()); d["files"]["memmap.tsv"] = "1" * 64; p.write_text(json.dumps(d, indent=2) + "\n"); case["inputs"]["provenance.json"] = __import__("hashlib").sha256(p.read_bytes()).hexdigest()'
expect_rejection unknown-reason "unknown result" \
  'case["expected"]["madt"]["result"] = "admission-rejected:tooManyCores"'
expect_rejection result-word-drift "disagrees with words" \
  'case["expected"]["madt"]["words"][2] = 1'
expect_rejection accepted-status-drift "accepted result needs status 1" \
  'case["expected"]["handoff"]["words"][1] = 2'
expect_rejection executing-id-drift "apic.executing differs from the capture" \
  'case["apic"]["executing"] = 7'
expect_rejection mutation-accepted "must name a typed rejection" \
  'case["mutations"]["madt-checksum"] = "accepted"'
expect_rejection mutation-unknown "names an unknown madt rejection" \
  'case["mutations"]["madt-checksum"] = "decoder-rejected:badVibes"'
expect_rejection mutation-missing "mutations must pin a result for each of" \
  'del case["mutations"]["madt-checksum"]'
expect_rejection root-stage "root_tables must be" \
  'case["root_tables"] = "acpidump"'
expect_rejection missing-permission "missing permission" \
  'case["permission"] = " "'

# Normalized-byte drift: a recorded digest that disagrees with conversion.
copy="$tmp/normalized-drift"
rm -rf "$copy" && cp -r firmware-corpus "$copy"
python3 - "$copy" <<'PY'
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
manifest = json.loads((root / "manifest.json").read_text())
manifest["cases"][0]["expected"]["handoff"]["normalized_sha256"] = "2" * 64
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
PY
if python3 "$tool" --manifest "$copy/manifest.json" normalize --out "$tmp/drift-out" > "$tmp/drift.log" 2>&1; then
  echo "error: normalized-byte drift was accepted" >&2
  exit 1
fi
grep -q "normalized handoff bytes differ from the recorded sha256" "$tmp/drift.log" || {
  echo "error: normalized-byte drift failed for the wrong reason" >&2
  cat "$tmp/drift.log" >&2
  exit 1
}

# An unknown E820 type name must reject rather than map to reserved.
copy="$tmp/unknown-e820"
rm -rf "$copy" && cp -r firmware-corpus "$copy"
python3 - "$copy" <<'PY'
import json, hashlib, sys
from pathlib import Path
root = Path(sys.argv[1])
manifest = json.loads((root / "manifest.json").read_text())
case = manifest["cases"][0]
path = root / case["id"] / "memmap.tsv"
path.write_text(path.read_text().replace("System RAM", "System RAM (mystery)", 1))
case["inputs"]["memmap.tsv"] = hashlib.sha256(path.read_bytes()).hexdigest()
prov = root / case["id"] / "provenance.json"
d = json.loads(prov.read_text()); d["files"]["memmap.tsv"] = case["inputs"]["memmap.tsv"]
prov.write_text(json.dumps(d, indent=2) + "\n")
case["inputs"]["provenance.json"] = hashlib.sha256(prov.read_bytes()).hexdigest()
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
PY
if python3 "$tool" --manifest "$copy/manifest.json" normalize --out "$tmp/unknown-out" > "$tmp/unknown.log" 2>&1; then
  echo "error: an unknown E820 type name was converted" >&2
  exit 1
fi
grep -q "unknown E820 type" "$tmp/unknown.log" || {
  echo "error: unknown E820 type failed for the wrong reason" >&2
  cat "$tmp/unknown.log" >&2
  exit 1
}
echo "Firmware handoff corpus checks passed: $cases cases, $rows replay rows, Lean checks and validator fixtures green"
