#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$repo_root/build/boundary-experiments"
cd "$repo_root"
lean_prefix="$(lean --print-prefix)"

for tool in lake lean leanc cc ld nm stat ldd; do
  command -v "$tool" >/dev/null || {
    echo "error: required tool not found: $tool" >&2
    exit 1
  }
done

rm -rf "$build_dir"
mkdir -p "$build_dir/direct" "$build_dir/hosted"

lake env lean -DwarningAsError=true -R "$repo_root/experiments/freestanding-boundary" \
  -c "$build_dir/direct/Boundary.c" \
  "$repo_root/experiments/freestanding-boundary/Boundary.lean"
cc -ffreestanding -fno-stack-protector -fno-pic -ffunction-sections \
  -fdata-sections -I"$lean_prefix/include" \
  -c "$build_dir/direct/Boundary.c" -o "$build_dir/direct/Boundary.o"
cc -ffreestanding -fno-stack-protector -fno-pic -ffunction-sections \
  -fdata-sections \
  -c "$repo_root/experiments/freestanding-boundary/primitives.c" \
  -o "$build_dir/direct/primitives.o"
cc -c "$repo_root/experiments/freestanding-boundary/entry.S" \
  -o "$build_dir/direct/entry.o"
ld -static --gc-sections -e _start -o "$build_dir/direct/direct.elf" \
  "$build_dir/direct/entry.o" "$build_dir/direct/Boundary.o" \
  "$build_dir/direct/primitives.o"

if nm -u "$build_dir/direct/direct.elf" | grep -q .; then
  echo "error: direct boundary has unresolved symbols" >&2
  nm -u "$build_dir/direct/direct.elf" >&2
  exit 1
fi
"$build_dir/direct/direct.elf"

lake env lean -DwarningAsError=true -R "$repo_root/experiments/hosted-boundary" \
  -c "$build_dir/hosted/Hosted.c" \
  "$repo_root/experiments/hosted-boundary/Hosted.lean"
leanc -o "$build_dir/hosted/hosted" "$build_dir/hosted/Hosted.c"
hosted_output="$($build_dir/hosted/hosted)"
test "$hosted_output" = "LEANOS-HOSTED result=90"

lean --version
cc --version | head -n 1
ld --version | head -n 1
stat -c '%n: %s bytes' \
  "$build_dir/direct/Boundary.c" "$build_dir/direct/Boundary.o" \
  "$build_dir/direct/direct.elf" "$build_dir/hosted/Hosted.c" \
  "$build_dir/hosted/hosted"
echo "$hosted_output"
ldd "$build_dir/hosted/hosted"
echo "Boundary experiments passed"
