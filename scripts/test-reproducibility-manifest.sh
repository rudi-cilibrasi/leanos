#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mapfile -t artifacts < <("$repo_root/scripts/write-reproducibility-manifest.sh" --list)

for artifact in "${artifacts[@]}"; do
  printf 'stable:%s\n' "$artifact" >"$fixture/$artifact"
done
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/first" "$fixture"
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/second" "$fixture"
"$repo_root/scripts/compare-reproducibility-manifests.sh" \
  "$fixture/first" "$fixture/second"

# Replay the real declared artifact inventory through actual shard hashing and
# the unchanged byte-comparison gate, including its declaration order.
printf '%s\n' "${artifacts[@]}" > "$fixture/artifacts.txt"
python3 "$repo_root/scripts/reproducibility-partitions.py" plan \
  "$fixture/artifacts.txt" --partitions 4 \
  --source-revision 0123456789012345678901234567890123456789 \
  --toolchain-id clang-reference@18.1.3 > "$fixture/plan.json"
results=()
for partition in 0 1 2 3; do
  result="$fixture/result-$partition.json"
  python3 "$repo_root/scripts/reproducibility-partitions.py" result \
    "$fixture/plan.json" --partition "$partition" --build-root "$fixture" > "$result"
  results+=("$result")
done
python3 "$repo_root/scripts/reproducibility-partitions.py" verify \
  "$fixture/plan.json" "${results[@]}" --artifacts "$fixture/artifacts.txt" \
  > "$fixture/aggregate"
"$repo_root/scripts/compare-reproducibility-manifests.sh" \
  "$fixture/first" "$fixture/aggregate"

printf 'nondeterministic\n' >>"$fixture/${artifacts[0]}"
"$repo_root/scripts/write-reproducibility-manifest.sh" "$fixture/changed" "$fixture"
if "$repo_root/scripts/compare-reproducibility-manifests.sh" \
  "$fixture/first" "$fixture/changed" 2>/dev/null; then
  echo "error: injected build-output nondeterminism was accepted" >&2
  exit 1
fi

rm "$fixture/${artifacts[1]}"
if "$repo_root/scripts/write-reproducibility-manifest.sh" \
  "$fixture/missing" "$fixture" 2>/dev/null; then
  echo "error: missing artifact was accepted" >&2
  exit 1
fi
python3 "$repo_root/scripts/test-reproducibility-partitions.py"
echo "Reproducibility manifest is stable, complete, and change-sensitive"
