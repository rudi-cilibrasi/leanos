#!/usr/bin/env bash
# Controlled negatives for the generated serial-protocol vocabulary: the
# renderer rejects malformed, duplicate, or lying rows; the shell fragment
# sources under set -u and its lookup helper fails loudly for a record that is
# not in the vocabulary; and no kernel source, assembly source, runner script,
# checker, or fixture spells a vocabulary record identity by hand.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
tab=$'\t'
# Record identities in this script are assembled from a split prefix so the
# universal literal scan below has nothing to flag in its own fixtures.
p='LEANOS/'
pe='LEANOS\/'

expect_rejection() {
  local target="$1" diagnostic="$2" input="$3"
  if printf '%b' "$input" |
      awk -v "target=$target" -f scripts/render-serial-protocol.awk > /dev/null 2> "$tmp/error"; then
    echo "error: render-serial-protocol.awk accepted: $diagnostic" >&2
    exit 1
  fi
  grep -Fxq "error: $diagnostic" "$tmp/error" || {
    echo "error: render-serial-protocol.awk failed without the expected diagnostic: $diagnostic" >&2
    cat "$tmp/error" >&2
    exit 1
  }
}

header='leanos-serial-protocol\t1\nsource-revision\ttest\n'
rows="${header}family\t3\tLEANOS_SERIAL_FAMILY_3\t${p}3\nrecord\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t${p}3 ORACLE\nrecord\t23\tREVOKE-DENIAL\tLEANOS_SERIAL_23_REVOKE_DENIAL\t${p}23 REVOKE-DENIAL\n"
printf '%b' "$rows" | awk -v target=h -f scripts/render-serial-protocol.awk > "$tmp/serial.h"
grep -Fxq "#define LEANOS_SERIAL_FAMILY_3 \"${p}3\"" "$tmp/serial.h"
grep -Fxq "#define LEANOS_SERIAL_23_REVOKE_DENIAL \"${p}23 REVOKE-DENIAL\"" "$tmp/serial.h"
grep -Fxq '#define LEANOS_SERIAL_RECORD_COUNT 2U' "$tmp/serial.h"
printf '%b' "$rows" | awk -v target=sh -f scripts/render-serial-protocol.awk > "$tmp/serial.sh"
(
  set -u
  # shellcheck source=/dev/null
  source "$tmp/serial.sh"
  [[ "$LEANOS_SERIAL_3_ORACLE" == "${p}3 ORACLE" ]]
  [[ "$(leanos_serial 23 REVOKE-DENIAL)" == "${p}23 REVOKE-DENIAL" ]]
  [[ "$(leanos_serial_re 23 REVOKE-DENIAL)" == "${pe}23 REVOKE-DENIAL" ]]
  [[ "$(leanos_serial_family_re 3)" == "${pe}3" ]]
  if value="$(leanos_serial 2 BOOT 2> /dev/null)"; then
    echo "error: a record outside the vocabulary resolved to '$value'" >&2
    exit 1
  fi
)
expect_rejection h "unexpected serial protocol schema: leanos-serial-protocol${tab}2" \
  'leanos-serial-protocol\t2\n'
expect_rejection h 'generated serial record prefix does not denote its identity: LEANOS_SERIAL_3_ORACLE' \
  "${header}record\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t${p}3 FINAL\n"
expect_rejection h 'duplicate generated serial record: LEANOS_SERIAL_3_ORACLE' \
  "${header}record\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t${p}3 ORACLE\nrecord\t3\tORACLE\tLEANOS_SERIAL_3_ORACLE\t${p}3 ORACLE\n"
expect_rejection h "malformed generated serial record row: record${tab}3${tab}oracle${tab}LEANOS_SERIAL_3_oracle${tab}${p}3 oracle" \
  "${header}record\t3\toracle\tLEANOS_SERIAL_3_oracle\t${p}3 oracle\n"
expect_rejection h "malformed generated serial family row: family${tab}3${tab}LEANOS_SERIAL_FAMILY_4${tab}${p}3" \
  "${header}family\t3\tLEANOS_SERIAL_FAMILY_4\t${p}3\n"
expect_rejection sh 'generated serial protocol vocabulary is empty' "$header"

# The generated vocabulary from the real model; every family it names is a
# family that no source may spell literally.
LEANOS_ORACLE_TOOL_SIGNATURE=test ./scripts/generate-oracle.sh "$tmp/out" > /dev/null
families="$(awk -F "$tab" '$1 == "family" { print $2 }' "$tmp/out/serial-protocol.tsv" | paste -sd '|')"
test -n "$families"
test "$(grep -c '^record' "$tmp/out/serial-protocol.tsv")" -ge 100
literal_pattern="LEANOS\\\\*/($families)([^0-9]|\$)"
scan() {
  local status=0
  grep -En "$literal_pattern" "$@" > "$tmp/literals" 2> "$tmp/literals.error" || status=$?
  if [[ $status -eq 0 ]]; then
    cat "$tmp/literals" >&2
    echo "error: hand-written serial record identity in: $*" >&2
    return 1
  elif [[ $status -ne 1 ]]; then
    cat "$tmp/literals.error" >&2
    echo "error: serial literal scan did not complete (grep status $status)" >&2
    return 1
  fi
}
mapfile -t sources < <(
  find boot -type f \( -name '*.c' -o -name '*.S' -o -name '*.h' \) | sort
  find scripts -type f \( -name '*.sh' -o -name '*.py' \) | sort
  find tests -type f -name '*.sh' | sort
)
test "${#sources[@]}" -gt 0
scan "${sources[@]}"
[[ ! -e boot/serial-protocol.h ]]
for mutation in \
  "serial_puts(\"${p}23 ENTER subject=1\\n\");" \
  "    .ascii \"${p}17 NMI reason=x\\n\"" \
  "echo '${p}10 BOOT target=x86_64-q35' > \"\$expected\"" \
  "sed -i '/^${pe}8 PAGING /d' \"\$log\"" \
  "marker = f\"${p}3 ORACLE id={row} result=PASS\""; do
  printf '%s\n' "$mutation" > "$tmp/mutated.c"
  if scan "$tmp/mutated.c" 2> /dev/null; then
    echo "error: a hand-written serial record was not rejected: $mutation" >&2
    exit 1
  fi
done
# A stale forgery of a family that is not in the vocabulary is allowed in a
# fixture, and the generic family wildcard used by the runners is not a
# literal identity.
printf '%s\n' "printf '%s\\n' '${p}2 BOOT target=x86_64-q35 entry=int80'" \
  "grep -Eq 'LEANOS/[0-9]+ FINAL ' \"\$log\"" > "$tmp/benign.sh"
scan "$tmp/benign.sh"
if scan "$tmp/benign.sh" "$tmp/does-not-exist.sh" 2> /dev/null; then
  echo "error: a scan error (missing operand) was accepted as a clean scan" >&2
  exit 1
fi
echo "Generated serial protocol vocabulary rejects drift and hand-written record identities"
