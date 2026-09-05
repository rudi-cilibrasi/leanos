#!/usr/bin/env bash
# Rendering of a boot scenario's expected serial transcript from its template
# in scripts/expectations/<boot scenario>.transcript (referenced from the
# scenario manifest). Sourced by scripts/run-image.sh and by
# scripts/check-expectation-templates.sh after the generated serial vocabulary
# (serial-protocol.sh); the caller sets `corpus` to the oracle corpus and the
# variables named in expectation_variables that its scenario needs.
#
# Template lines are one record each: @<family>/<TAG>@<rest> renders the
# record prefix through leanos_serial, @var:<name>@ substitutes an allowlisted
# runner variable, and the named markers below expand to the segments every
# boot scenario shares, which are spelled once here.
expectation_common_prefix() {
  printf '%s\n' \
    "${LEANOS_SERIAL_15_DMA} snapshot=1 topology=0001000800020002 bus=0 scanned=256 present=5 optional-absent=1 writes=5 readbacks=5 initial-bus-masters=1 initial-bus-master-mask=16 bus-master=disabled readback=exact generated-result=0 stage=pre-cpl3 result=PASS" \
    "${LEANOS_SERIAL_8_PAGING} root=A selected=1 leaves=4096 policy=manifest result=PASS" \
    "${LEANOS_SERIAL_8_PAGING} root=B selected=0 leaves=4096 policy=manifest result=PASS" \
    "${LEANOS_SERIAL_19_TLB} path=invlpg address-space=2 page=7 pte=cleared order=store,invlpg,publish before=309063438 after=308959202 result=PASS" \
    "${LEANOS_SERIAL_19_TLB} path=cr3 address-space=2 page=7 pte=cleared order=store,cr3,publish before=309063438 after=308959202 result=PASS" \
    "${LEANOS_SERIAL_19_TLB} authority=generated-composite effect=page address-space=2 page=7 window=restored result=PASS" \
    "${LEANOS_SERIAL_19_TLB} mutable-leaf=checked address-space=2 page=7 states=boot,before,unmapped,after immutable-leaves=exact result=PASS"
}
expectation_common_oracle() {
  awk -F '\t' "\$1 ~ /^[0-9]+\$/ { print \"${LEANOS_SERIAL_3_ORACLE} id=\" \$2 \" result=PASS\" }" "$corpus"
}
expectation_common_pre_cpl3() {
  printf '%s\n' \
    "${LEANOS_SERIAL_17_ENTRY_MANIFEST} ordinary=8 extended=6,7 contained=0,3 auxiliary=1 terminal=2 extra=0 rsp0=entry-stack ist1=df-stack ist2=nmi-stack result=PASS" \
    "${LEANOS_SERIAL_16_DIRECT_PORT_CONTROL} tr=40 limit=103 iomap=104 bitmap=absent iopl=0 stage=pre-cpl3 result=PASS"
}
expectation_common_controls() {
  printf '%s\n' \
    "${LEANOS_SERIAL_6_CONTROL} cr0.wp=1 cr0.em=1 cr0.mp=1 cr0.ts=1 cr4.osfxsr=0 cr4.osxmmexcpt=0 cr4.osxsave=0 cr4.pke=0 cr4.smep=1 cr4.smap=1 ac=0 stage=exception-path-ready" \
    "${LEANOS_SERIAL_4_PROBE} kind=wp vector=14 error=3 origin=kernel address=kernel-text policy=fatal result=PASS" \
    "${LEANOS_SERIAL_4_PROBE} kind=smep vector=14 error=17 origin=kernel address=user-a-text policy=fatal result=PASS" \
    "${LEANOS_SERIAL_6_PROBE} kind=smap-direct vector=14 origin=kernel ac=0 result=PASS" \
    "${LEANOS_SERIAL_6_POLICY} zero=accept max=accept unmapped=reject readonly=reject overflow=reject noncanonical=reject wrong-subject=reject stale=reject atomic=PASS" \
    "${LEANOS_SERIAL_6_CLEANUP} omitted=detected wrappers=checked entry=clac result=PASS"
}
expectation_variables=(
  frame_budget_physical frame_budget_boot_physical
  fault_page fault_leaf fault_address
  stale_translation_cr3 stale_translation_rip stale_translation_rsp
)
render_expectation() {
  local template="$1" line rest name value candidate
  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      '@common:prefix@') expectation_common_prefix ;;
      '@common:oracle@') expectation_common_oracle ;;
      '@common:pre-cpl3@') expectation_common_pre_cpl3 ;;
      '@common:controls@') expectation_common_controls ;;
      *)
        if [[ "$line" =~ ^@([0-9]+)/([A-Z][A-Z0-9-]*)@(.*)$ ]]; then
          rest="${BASH_REMATCH[3]}"
          line="$(leanos_serial "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}")$rest"
        else
          echo "failure_class=runner-template: line does not start with a record placeholder: $line" >&2
          exit 1
        fi
        while [[ "$line" =~ @var:([a-z0-9_]+)@ ]]; do
          name="${BASH_REMATCH[1]}"
          value=""
          for candidate in "${expectation_variables[@]}"; do
            [[ "$candidate" == "$name" ]] && value="${!name:-}"
          done
          [[ -n "$value" ]] || {
            echo "failure_class=runner-template: unknown or unset expectation variable $name" >&2
            exit 1
          }
          line="${line//@var:${name}@/$value}"
        done
        printf '%s\n' "$line"
        ;;
    esac
  done < "$template"
}
