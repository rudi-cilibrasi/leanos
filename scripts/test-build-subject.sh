#!/usr/bin/env bash
# The subject build rule (#484): the template, the example and the endpoint
# directory (#485) each build into a slot object, and every negative fixture
# under subjects/fixtures is rejected at build time with the expected reason.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
cc="${LEANOS_CC:-gcc}"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

for subject in template example directory; do
  ./scripts/build-subject.sh --cc "$cc" --slot c --output "$work/$subject.o" \
    "subjects/$subject"
  symbols="$(nm "$work/$subject.o")"
  for symbol in user_c_entry user_c_stack user_c_stack_top user_c_template_text; do
    grep -Eq "^[0-9a-f]+ [TDB] $symbol$" <<<"$symbols" || {
      echo "error: $subject slot object lacks global $symbol" >&2; exit 1;
    }
  done
  # Everything else is local, so nothing in the subject can collide with or
  # resolve against a kernel symbol.
  if grep -Ev '^[0-9a-f]+ [a-z] |user_c_(entry|stack|stack_top|template_text)$' \
      <<<"$symbols" | grep -q .; then
    echo "error: $subject slot object exports unexpected symbols" >&2; exit 1
  fi
  sections="$(readelf -SW "$work/$subject.o")"
  grep -Eq '\.user\.c\.text +PROGBITS .* AX ' <<<"$sections" &&
    grep -Eq '\.user\.c\.bss +(PROGBITS|NOBITS) +[0-9a-f]+ [0-9a-f]+ 001000 .* WA ' <<<"$sections" || {
      echo "error: $subject slot object sections are not the slot layout" >&2; exit 1;
    }
done

# fixture <TAB> reason the rule must report
fixtures=(
  $'privileged-cli\t[privileged or system instruction]'
  $'privileged-wrmsr\t[privileged or system instruction]'
  $'privileged-stac\t[privileged or system instruction]'
  $'port-io\t[port I/O]'
  $'fast-entry\t[privileged or system instruction]'
  $'other-vector\t[kernel entry other than int $0x80]'
  $'control-register\t[control, debug or test register access]'
  $'extended-state\t[x87/MMX/SSE/AVX state (denied at CPL3)]'
  $'libc-call\tundefined symbols (no libc, no kernel symbols): puts'
  $'oversized-data\tcannot move location counter backwards'
)
seen=0
for row in "${fixtures[@]}"; do
  IFS=$'\t' read -r fixture reason <<<"$row"
  [[ -d "subjects/fixtures/$fixture" ]] || {
    echo "error: missing negative fixture subjects/fixtures/$fixture" >&2; exit 1;
  }
  if ./scripts/build-subject.sh --cc "$cc" --slot c \
      --output "$work/$fixture.o" "subjects/fixtures/$fixture" \
      >"$work/$fixture.log" 2>&1; then
    echo "error: build rule accepted negative fixture $fixture" >&2; exit 1
  fi
  grep -Fq -- "$reason" "$work/$fixture.log" || {
    echo "error: negative fixture $fixture was rejected for the wrong reason:" >&2
    cat "$work/$fixture.log" >&2
    exit 1
  }
  [[ ! -e "$work/$fixture.o" ]] || {
    echo "error: rejected fixture $fixture left an object behind" >&2; exit 1;
  }
  seen=$((seen + 1))
done
# Every fixture directory is exercised.
count="$(find subjects/fixtures -mindepth 1 -maxdepth 1 -type d | wc -l)"
[[ "$count" -eq "$seen" ]] || {
  echo "error: subjects/fixtures has $count fixtures, the test covers $seen" >&2; exit 1;
}

printf 'build-subject\tPASS\tsubjects=3\tnegative-fixtures=%s\n' "$seen"
