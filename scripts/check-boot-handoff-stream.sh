#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
id="${LEANOS_HOSTED_BOUNDARY_ID:-freestanding-stream}"
manifest=scripts/hosted-generated-boundaries.tsv
source scripts/hosted-boundary-coverage.sh
row="$(awk -F '\t' -v id="$id" '$1 == id { print; found=1 } END { exit !found }' "$manifest")" || {
  echo "error: hosted boundary '$id' is absent from $manifest" >&2
  exit 1
}
IFS=$'\t' read -r _ _ harness generation target modules exports assertion <<<"$row"
[[ "$id" == freestanding-stream && "$generation" == lake-ir ]] || {
  echo "error: $id is not the lake-ir freestanding-stream boundary" >&2
  exit 1
}
[[ "$modules" == BootMemoryMapStreaming,BootMemoryMapStreamAuthority ]] || {
  echo "error: freestanding stream generated-module inventory changed" >&2
  exit 1
}

case "$mode" in
  ordinary) build=build/boot-handoff-stream ;;
  sanitized)
    source scripts/hosted-sanitizer-config.sh
    leanos_assert_pinned_toolchain
    build=build/boot-handoff-stream-sanitized
    ;;
  *)
    echo "usage: $0 [ordinary|sanitized]" >&2
    exit 2
    ;;
esac
rm -rf "$build"
mkdir -p "$build"

production_allocate="$(
  sed -n '/^static void boot_allocate(/,/^}/p' boot/kernel.c
)"
production_decode="$(
  sed -n '/^static struct boot_decode_state decode_boot_projection(/,/^}/p' boot/kernel.c
)"
for required in decode_boot_projection leanos_boot_projection_manifest \
  leanos_boot_projection_free projection_finish_query \
  decode_boot_candidate_authority leanos_boot_manifest_candidate \
  leanos_boot_consume_exact_projection leanos_boot_authority_result; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production allocation omits $required" >&2
    exit 1
  }
done
for required in \
  'for (uint64_t candidate = 0; candidate < 4096; ++candidate)' \
  'uint64_t exact_candidate = leanos_boot_consume_exact_projection(' \
  'selected = exact_candidate' \
  'next_selected = exact_candidate' \
  'frame_budget_physical_frame = next_selected' \
  'authority.word[3] != selected'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production selection is not bound to the canonical raw-byte candidate scan: $required" >&2
    exit 1
  }
done
if grep -Fq 'selected = authority.word[3]' <<<"$production_allocate"; then
  echo "error: production selected a caller-transported projection word" >&2
  exit 1
fi
if grep -Fq 'frame_budget_physical_frame = authority.word[8]' \
    <<<"$production_allocate"; then
  echo "error: frame-budget allocation consumed a caller-transported projection word" >&2
  exit 1
fi
for required in \
  'LEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE' \
  'const uint64_t exact_replay_selected = selected' \
  'authority.word[3] = selected == 4095 ? selected - 1 : selected + 1' \
  'selected != exact_replay_selected' \
  'handoff_fail("projection-mutation-raw-selection")'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production projection-selection mutation fixture omits $required" >&2
    exit 1
  }
done
mutation_line="$(grep -n 'authority.word\[3\] = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
rejection_line="$(grep -n 'authority.word\[3\] != selected' <<<"$production_allocate" | cut -d: -f1)"
scrub_line="$(grep -n 'frame\[i\] = 0' <<<"$production_allocate" | cut -d: -f1)"
publication_line="$(grep -n 'leanos_boot_authority_result(' <<<"$production_allocate" | tail -1 | cut -d: -f1)"
for required in \
  'LEANOS_RAW_SELECTION_MUTATION_FIXTURE' \
  'LEANOS_RAW_CLASSIFICATION_MUTATION_FIXTURE' \
  'selected_authority.word[16] != selected' \
  'LEANOS_PUBLICATION_RESULT_MUTATION_FIXTURE' \
  'publication.word[3] = selected == 4095 ? selected - 1 : selected + 1'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production raw-authority mutation coverage omits $required" >&2
    exit 1
  }
done
raw_selection_mutation_line="$(grep -n '^    selected = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
raw_selection_rejection_line="$(grep -n 'selected_authority.word\[16\] != selected' <<<"$production_allocate" | cut -d: -f1)"
raw_classification_mutation_line="$(grep -n 'selected_authority.word\[14\] = 0' <<<"$production_allocate" | cut -d: -f1)"
publication_mutation_line="$(grep -n 'publication.word\[3\] = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
publication_rejection_line="$(grep -n 'publication.word\[3\] != selected' <<<"$production_allocate" | cut -d: -f1)"
if (( raw_selection_mutation_line >= raw_selection_rejection_line ||
      raw_classification_mutation_line >= raw_selection_rejection_line ||
      raw_selection_rejection_line >= scrub_line ||
      publication_mutation_line >= publication_rejection_line )); then
  echo "error: production raw-authority mutation can reach authority use before rejection" >&2
  exit 1
fi
if (( mutation_line >= rejection_line || rejection_line >= scrub_line ||
      rejection_line >= publication_line )); then
  echo "error: projection-selection mutation can reach scrub/publication before rejection" >&2
  exit 1
fi
if grep -Eq 'mb2_(tag|mmap)|boot_frames|reserve_byte_range|allocation_check' \
    <<<"$production_allocate"; then
  echo "error: production allocation retained a C handoff policy authority" >&2
  exit 1
fi
production_authority="$(
  sed -n '/^static struct boot_decode_state decode_boot_candidate_authority(/,/^}/p' boot/kernel.c
)"
for required in 'query < 23' 'state.word[16] != candidate' \
  'candidate_authority.word[14]' 'candidate_authority.word[15]' \
  'selected_authority.word[14] != 1' \
  'selected_authority.word[15] != 0'; do
  grep -Fq "$required" <<<"$production_allocate$production_authority" || {
    echo "error: production selected-frame authorization omits $required" >&2
    exit 1
  }
done
grep -Fq 'struct boot_decode_state { uint64_t word[23]; };' boot/kernel.c || {
  echo "error: production decoder does not retain parser state plus typed entry event" >&2
  exit 1
}
for required in 'query < 23' 'state.word[0] != 4' \
  'state.word[18], info_address'; do
  grep -Fq "$required" <<<"$production_decode" || {
    echo "error: production decoder omits scalar ABI v4 tag-count state: $required" >&2
    exit 1
  }
done
grep -Fq \
  'def entryLimit : UInt64 := UInt64.ofNat LeanOS.BootMemoryMap.maxEntries' \
  LeanOS/BootMemoryMapStreamAuthority.lean || {
  echo "error: production decoder entry limit is not derived from the rich model" >&2
  exit 1
}
if grep -Fq 'MAX_MMAP_ENTRIES' boot/kernel.c; then
  echo "error: production C retains a second memory-map entry limit" >&2
  exit 1
fi

IFS=',' read -ra targets <<<"$target"
lake build "${targets[@]}" LeanOS.BootMemoryMapStreamPipeline
prefix="$(lake env lean --print-prefix)"

if [[ "$mode" == sanitized ]]; then
  leanos_prepare_boundary_coverage "$build" "$exports"
  objects=()
  IFS=',' read -ra module_names <<<"$modules"
  mapfile -t compiled_modules < <(
    leanos_project_module_closure "${module_names[@]}"
  )
  for module in "${compiled_modules[@]}"; do
    source=".lake/build/ir/LeanOS/$module.c"
    object_name="${module//\//_}"
    [[ -f "$source" ]] || {
      echo "error: generated module inventory is missing $source" >&2
      exit 1
    }
    "$leanos_host_cc" -std=c11 "${leanos_host_sanitizer_flags[@]}" \
      -finstrument-functions \
      -I"$prefix/include" -c "$source" -o "$build/$object_name.o"
    leanos_require_sanitized_object "$build/$object_name.o"
    objects+=("$build/$object_name.o")
  done
  "$leanos_host_cc" -std=c11 -Wall -Wextra -Werror \
    "${leanos_host_sanitizer_flags[@]}" -finstrument-functions \
    -DLEANOS_HOSTED_REPLAY=1 -DLEANOS_HOSTED_SANITIZER=1 \
    -c "$harness" -o "$build/host.o"
  "$leanos_host_cc" -std=c11 -Wall -Wextra -Werror \
    -c "$build/boundary-coverage.c" -o "$build/boundary-coverage.o"
  leanos_link_sanitized_host "$build/host" "$build/host.o" \
    "$build/boundary-coverage.o" "${objects[@]}"
  LEANOS_BOUNDARY_COVERAGE_FILE="$build/boundary-coverage.actual" \
    leanos_run_sanitized "$build/host" | tee "$build/results.txt"
  leanos_check_boundary_coverage "$build"
  expected="${assertion#contains=}"
  expected="${expected//_/ }"
  [[ "$assertion" == contains=* ]] && grep -Fq "$expected" "$build/results.txt" || {
    echo "error: hosted freestanding-stream replay lacked '$expected'" >&2
    exit 1
  }
  ordinary=build/boot-handoff-stream/results.txt
  [[ -f "$ordinary" ]] || {
    echo "error: ordinary freestanding-stream results are required before sanitized replay" >&2
    exit 1
  }
  if ! cmp -s "$ordinary" "$build/results.txt"; then
    first="$(
      paste "$ordinary" "$build/results.txt" |
        awk -F '\t' '$1 != $2 { print NR; exit }'
    )"
    operation="$(sed -n "${first}p" "$ordinary" | awk '{print $2}')"
    echo "error: freestanding-stream replay first diverged at operation/field $operation (row $first)" >&2
    sed -n "${first}p" "$ordinary" | sed 's/^/ordinary: /' >&2
    sed -n "${first}p" "$build/results.txt" |
      sed 's/^/sanitized: /' >&2
    exit 1
  fi
  echo "Hosted generated-C freestanding stream sanitized replay passed"
  exit 0
fi

cflags=(-m64 -std=c11 -O2 -ffreestanding -fno-stack-protector -fno-pic
  -mno-red-zone -ffunction-sections -fdata-sections -Wall -Wextra -Werror)

lake env leanc "${cflags[@]}" -I"$prefix/include" \
  -c .lake/build/ir/LeanOS/BootMemoryMapStreaming.c -o "$build/stream.o"
lake env leanc "${cflags[@]}" -I"$prefix/include" \
  -c .lake/build/ir/LeanOS/BootMemoryMapStreamAuthority.c -o "$build/authority.o"
cc "${cflags[@]}" -c tests/boot-handoff-stream-freestanding.c -o "$build/test.o"
cc -m64 -std=c11 -O2 -Wall -Wextra -Werror \
  -DLEANOS_HOSTED_REPLAY=1 \
  -c tests/boot-handoff-stream-freestanding.c -o "$build/host.o"
cc -m64 -nostdlib -static -no-pie -Wl,--gc-sections -Wl,-e,_start \
  "$build/test.o" "$build/stream.o" "$build/authority.o" -o "$build/stream.elf"
cc -m64 -no-pie -Wl,--gc-sections \
  "$build/host.o" "$build/stream.o" "$build/authority.o" -o "$build/host"

undefined="$(nm -u "$build/stream.elf")"
if [[ -n "$undefined" ]]; then
  echo "error: handoff stream image has unexpected undefined symbols:" >&2
  echo "$undefined" >&2
  exit 1
fi

symbols="$(nm "$build/stream.elf")"
for symbol in leanos_boot_handoff_stream_init leanos_boot_handoff_stream_step \
  leanos_boot_decode_init leanos_boot_decode_step leanos_boot_manifest_candidate \
  leanos_boot_manifest_start leanos_boot_consume_exact_projection \
  leanos_boot_publish_authority leanos_boot_authority_result \
  leanos_boot_projection_entry \
  leanos_boot_projection_manifest leanos_boot_projection_free \
  leanos_boot_projection_finish; do
  if ! grep -q " T ${symbol}$" <<<"$symbols"; then
    echo "error: handoff stream image does not retain $symbol" >&2
    exit 1
  fi
done

# This focused final ELF retains only the version-two transport decision
# boundary.  In particular, neither the boxed whole-buffer reader nor the old
# scalar allocation-policy adapter may become an accidental second authority.
for forbidden_policy in leanos_boot_handoff_query leanos_boot_handoff_fixture_query \
  leanos_boot_allocation_check leanos_boot_select_frame; do
  if grep -q " T ${forbidden_policy}$" <<<"$symbols"; then
    echo "error: handoff stream image retained forbidden policy symbol $forbidden_policy" >&2
    exit 1
  fi
done

# Inventory every retained text symbol so a static C parser/classifier cannot
# hide behind a non-exported name in this final focused artifact.
while read -r text_symbol; do
  case "$text_symbol" in
    _start|check_stream|decode|decode_entry_count|decode_extent|expect_decode_error|step_query|\
leanos_boot_handoff_stream_init|\
leanos_boot_handoff_stream_step|\
leanos_boot_decode_init|leanos_boot_decode_step|leanos_boot_manifest_candidate|\
leanos_boot_manifest_start|\
leanos_boot_consume_exact_projection|leanos_boot_publish_authority|\
leanos_boot_authority_result|\
leanos_boot_projection_entry|leanos_boot_projection_manifest|\
leanos_boot_projection_free|leanos_boot_projection_finish|\
lp_leanos___private_LeanOS_BootMemoryMapStreaming_0__LeanOS_BootMemoryMapStreaming_canonicalChunk|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_manifestValid|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_firstInEight|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_firstInSixtyFour|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_firstAfterInSixtyFour|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_firstSetBit|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_maskAfter|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_reservationMaskWord|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_transitionError___redArg)
      ;;
    *)
      echo "error: unreviewed handoff stream text symbol $text_symbol" >&2
      exit 1
      ;;
  esac
done < <(awk '$2 == "T" || $2 == "t" { print $3 }' <<<"$symbols")

forbidden='lean_(alloc|box|mk_|dec|inc|nat|array|list|initialize|internal_panic)|mi_(malloc|calloc)|Nat_'
if grep -Eq "$forbidden" \
    <<<"$symbols"; then
  echo "error: handoff stream image retained allocation, boxed, Nat, or initialization runtime" >&2
  grep -E "$forbidden" <<<"$symbols" >&2
  exit 1
fi

"$build/stream.elf"
"$build/host" | tee "$build/results.txt"
echo "Freestanding generated-C handoff stream replay passed"
