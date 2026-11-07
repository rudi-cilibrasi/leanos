#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
cc="${LEANOS_CC:-gcc}"
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
# The handoff copy and decoder live in include/boot_handoff_decode.h (#624):
# boot_allocate checks the extent, observes the executing APIC ID, then copies
# and decodes the handoff through the header, and maps each status to the
# reason of its check.
handoff_decode=include/boot_handoff_decode.h
handoff_function() {
  sed -n "/^static inline [a-z_ ]* $1(/,/^}/p" "$handoff_decode"
}
production_extent="$(handoff_function boot_handoff_extent)"
production_handoff_copy="$(handoff_function boot_handoff_stream_copy)"
production_transition="$(handoff_function boot_decode_transition)"
production_decode="$(handoff_function boot_handoff_decode_projection)"
production_authority="$(handoff_function boot_handoff_decode_candidate)"
production_project="$(handoff_function boot_handoff_project)"
production_handoff_read="$(
  sed -n '/^static uint64_t boot_handoff_physical_read(/,/^}/p' boot/kernel.c
)"
for function in boot_handoff_extent boot_handoff_stream_copy \
  boot_decode_transition boot_handoff_decode_projection \
  boot_handoff_decode_candidate boot_handoff_project; do
  [[ -n "$(handoff_function "$function")" ]] || {
    echo "error: $handoff_decode does not define $function" >&2
    exit 1
  }
done
[[ -n "$production_handoff_read" ]] || {
  echo "error: boot/kernel.c does not define the handoff's physical read" >&2
  exit 1
}
# The root and table copy pipeline lives in include/acpi_table_copy.h (#614);
# boot_allocate calls it once and maps each status to its reason.
acpi_copy=include/acpi_table_copy.h
acpi_function() {
  sed -n "/^static inline enum acpi_table_copy_status $1(/,/^}/p" "$acpi_copy"
}
production_topology_copy="$(acpi_function acpi_copy_root_tables)"
production_physical_copy="$(
  sed -n '/^static void copy_acpi_physical_bytes(/,/^}/p' boot/kernel.c
)"
production_sdt_copy="$(acpi_function acpi_copy_sdt)"
production_root_addresses="$(acpi_function acpi_decode_root_addresses)"
production_pipeline="$(acpi_function acpi_copy_root_and_tables)"
# acpi_table_copy_require, one line per status: "status reason".
production_reasons="$(
  sed -n '/^static void acpi_table_copy_require(/,/^}/p' boot/kernel.c |
    tr '\n' ' ' | tr -s ' ' |
    grep -o 'if (status == ACPI_TABLE_COPY_[A-Z_]*) handoff_fail("[a-z0-9-]*")' |
    sed 's/if (status == \(ACPI_TABLE_COPY_[A-Z_]*\)) handoff_fail("\([a-z0-9-]*\)")/\1 \2/'
)"
require_reason() {  # status reason: the kernel fails the handoff with reason on status
  grep -Fxq "$1 $2" <<<"$production_reasons" || {
    echo "error: boot_allocate does not map $1 to reason $2" >&2
    exit 1
  }
}
for required in \
  'mov %%cr3' \
  '(uint64_t)page_map_level_4_a' \
  '(saved_leaf & PTE_PRESENT) == 0' \
  '(saved_leaf & PTE_USER) != 0' \
  'frame | PTE_PRESENT | PTE_WRITABLE | PTE_NX' \
  '((volatile uint64_t *)page_table_a)[window_page] = saved_leaf' \
  'handoff_fail("topology-sdt-address-space")'; do
  grep -Fq "$required" <<<"$production_physical_copy" || {
    echo "error: physical ACPI copy aperture omits active-root/leaf protection: $required" >&2
    exit 1
  }
done
grep -Fq 'copy_acpi_physical_bytes(physical_address, destination, length);' \
    <<<"$(sed -n '/^static int boot_acpi_physical_copy(/,/^}/p' boot/kernel.c)" || {
  echo "error: the ACPI copy pipeline's physical copy is not the aperture copy" >&2
  exit 1
}
for required in \
  'leanos_boot_machine_acpi_copy_stream_step_query(' \
  'next_byte != byte_offset + chunk_bytes' \
  'exposed != physical_chunk' \
  'destination[byte_offset + byte]' \
  'return ACPI_TABLE_COPY_ERROR;' \
  'return ACPI_TABLE_COPY_STATUS;' \
  'return ACPI_TABLE_COPY_NEXT_BYTE;' \
  'return ACPI_TABLE_COPY_EXPOSED;' \
  'return ACPI_TABLE_COPY_PARTIAL_CURSOR;' \
  'return ACPI_TABLE_COPY_FINAL_CURSOR;'; do
  grep -Fq "$required" <<<"$production_sdt_copy" || {
    echo "error: production SDT copy omits generated byte-stream binding: $required" >&2
    exit 1
  }
done
require_reason ACPI_TABLE_COPY_ERROR topology-table-copy-error
require_reason ACPI_TABLE_COPY_STATUS topology-table-copy-status
require_reason ACPI_TABLE_COPY_NEXT_BYTE topology-table-copy-next-byte
require_reason ACPI_TABLE_COPY_EXPOSED topology-table-copy-exposed
require_reason ACPI_TABLE_COPY_PARTIAL_CURSOR topology-table-copy-partial-cursor
require_reason ACPI_TABLE_COPY_FINAL_CURSOR topology-table-copy-final-cursor
for required in \
  'if (entries->count == 0)' \
  'uint64_t copied_ordinal = 0' \
  'leanos_boot_machine_acpi_copy_sequence_step_query(' \
  'copied_ordinal, entries->count, entry, 1, final_table, 1' \
  'copied_ordinal, entries->count, entry, 1, final_table, 2' \
  'copied_ordinal, entries->count, entry, 1, final_table, 3' \
  'next_ordinal != entry + 1u' \
  'return ACPI_TABLE_COPY_SEQUENCE;' \
  'copied_ordinal != entries->count'; do
  grep -Fq "$required" <<<"$production_topology_copy" || {
    echo "error: production table copies omit generated sequence binding: $required" >&2
    exit 1
  }
done
require_reason ACPI_TABLE_COPY_SEQUENCE topology-table-copy-sequence
# Every status of the header has its reason, and no reason two statuses.
mapfile -t acpi_statuses < <(
  sed -n '/^enum acpi_table_copy_status {/,/^};/p' "$acpi_copy" |
    grep -o 'ACPI_TABLE_COPY_[A-Z_]*' | grep -vx ACPI_TABLE_COPY_OK
)
[[ ${#acpi_statuses[@]} -gt 0 ]] || {
  echo "error: include/acpi_table_copy.h declares no failure status" >&2; exit 1;
}
for acpi_status in "${acpi_statuses[@]}"; do
  [[ "$(grep -c "^$acpi_status " <<<"$production_reasons")" -eq 1 ]] || {
    echo "error: boot_allocate maps $acpi_status to no reason, or to several" >&2
    exit 1
  }
done
[[ "$(wc -l <<<"$production_reasons")" -eq ${#acpi_statuses[@]} &&
   "$(cut -d' ' -f2 <<<"$production_reasons" | sort -u | wc -l)" -eq ${#acpi_statuses[@]} ]] || {
  echo "error: the ACPI copy statuses and their reasons are not one to one" >&2
  exit 1
}
for required in 'boot_handoff_require(boot_handoff_project(' \
  'boot_frame_require(boot_frame_terminal(' 'boot_frame_select(' \
  'boot_frame_require(boot_frame_cross_check(' \
  'boot_frame_require(boot_frame_scrub_selected(' \
  'boot_frame_publication_result(' \
  'boot_frame_require(boot_frame_publication_check(' 'boot_frame_rescan(' \
  'acpi_table_copy_require(acpi_copy_root_and_tables(' \
  'boot_acpi_physical_copy, 0, decoded.word[39], decoded.word[40],' \
  '.root = boot_acpi_root_copy,' \
  '.tables = boot_acpi_table_copy,' \
  '.copies = boot_acpi_table_copies'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production allocation omits $required" >&2
    exit 1
  }
done
for required in \
  '(selected_kind != 1 && selected_kind != 2) || selected_address == 0' \
  'return ACPI_TABLE_COPY_ROOT_SELECTION;' \
  'copy, context, selected_address, storage->header, storage->root,' \
  'selected_root->physical_address != selected_address' \
  'return ACPI_TABLE_COPY_ROOT_COPY;' \
  'acpi_decode_root_entries(selected_root, selected_kind,' \
  'acpi_decode_root_addresses(root_entries, root_table_addresses)' \
  'acpi_copy_root_tables(copy, context, root_entries,' \
  'copied_table_count != root_entries->count' \
  'return ACPI_TABLE_COPY_INCOMPLETE;' \
  'acpi_select_unique_madt(storage->copies, copied_table_count,'; do
  grep -Fq "$required" <<<"$production_pipeline" || {
    echo "error: the production ACPI copy pipeline omits $required" >&2
    exit 1
  }
done
for required in \
  'acpi_decode_root_entry(entries, entry, &addresses[entry])' \
  'addresses[prior] == addresses[entry]' \
  'return ACPI_TABLE_COPY_ROOT_ENTRY_DUPLICATE;'; do
  grep -Fq "$required" <<<"$production_root_addresses" || {
    echo "error: production root entry decoding omits $required" >&2
    exit 1
  }
done
require_reason ACPI_TABLE_COPY_ROOT_SELECTION topology-root-selection
require_reason ACPI_TABLE_COPY_ROOT_COPY topology-root-copy
require_reason ACPI_TABLE_COPY_ROOT_ENTRY_DUPLICATE topology-root-entry-duplicate
require_reason ACPI_TABLE_COPY_INCOMPLETE topology-table-copy-incomplete
root_copy_line="$(grep -n 'copy, context, selected_address, storage->header' <<<"$production_pipeline" | cut -d: -f1)"
root_vector_line="$(grep -n 'acpi_decode_root_entries(selected_root' <<<"$production_pipeline" | cut -d: -f1)"
root_entry_line="$(grep -n 'acpi_decode_root_addresses(root_entries' <<<"$production_pipeline" | cut -d: -f1)"
table_copy_line="$(grep -n 'acpi_copy_root_tables(copy, context' <<<"$production_pipeline" | cut -d: -f1)"
[[ -n "$root_copy_line" && -n "$root_vector_line" && -n "$root_entry_line" &&
   -n "$table_copy_line" && "$root_copy_line" -lt "$root_vector_line" &&
   "$root_vector_line" -lt "$root_entry_line" &&
   "$root_entry_line" -lt "$table_copy_line" ]] || {
  echo "error: the ACPI copy pipeline must copy the selected root and decode its entries before copying the tables" >&2
  exit 1
}
pipeline_line="$(grep -n 'acpi_table_copy_require(acpi_copy_root_and_tables(' <<<"$production_allocate" | cut -d: -f1)"
scrub_line="$(grep -n 'boot_frame_require(boot_frame_scrub_selected(' <<<"$production_allocate" | cut -d: -f1)"
[[ -n "$pipeline_line" && -n "$scrub_line" && "$pipeline_line" -lt "$scrub_line" ]] || {
  echo "error: production must copy the selected ACPI root and every advertised table before scrub/publication" >&2
  exit 1
}
# The canonical MADT admission lives in include/madt_generated_admission.h
# (#617): boot_allocate calls it once on the unique MADT copy, before the
# scrub, and maps each status to the reason of its step.
madt_admission=include/madt_generated_admission.h
for required in \
  'madt_generated_require(madt_generated_admission(' \
  'selected_madt->bytes, selected_madt->length,' \
  'handoff.executing_apic_id, decoded.word[39], decoded.word[40],' \
  'acpi.root.physical_address, acpi.entries.count, acpi.table_count,'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production allocation omits the generated MADT admission: $required" >&2
    exit 1
  }
done
madt_line="$(grep -n 'madt_generated_require(madt_generated_admission(' <<<"$production_allocate" | cut -d: -f1)"
[[ -n "$madt_line" && "$pipeline_line" -lt "$madt_line" && "$madt_line" -lt "$scrub_line" ]] || {
  echo "error: production must admit the copied MADT after the ACPI copy and before scrub/publication" >&2
  exit 1
}
production_madt_admission="$(
  sed -n '/^static inline enum madt_generated_status madt_generated_admission(/,/^}/p' "$madt_admission"
)"
madt_envelope_line="$(grep -n 'madt_generated_envelope(bytes, length)' <<<"$production_madt_admission" | cut -d: -f1)"
madt_entries_line="$(grep -n 'madt_generated_entries(bytes, length, executing_apic_id,' <<<"$production_madt_admission" | cut -d: -f1)"
madt_result_line="$(grep -n 'madt_topology_admission_result(' <<<"$production_madt_admission" | cut -d: -f1)"
[[ -n "$madt_envelope_line" && -n "$madt_entries_line" && -n "$madt_result_line" &&
   "$madt_envelope_line" -lt "$madt_entries_line" && "$madt_entries_line" -lt "$madt_result_line" ]] &&
  grep -Fq 'advertised_count, completed_copies, 1, 1, 0, admitted_apic_id,' \
    <<<"$production_madt_admission" || {
  echo "error: the MADT admission must run the envelope, then the entry stream, then the admission result" >&2
  exit 1
}
# madt_generated_require, one line per status: "status reason".
madt_reasons="$(
  sed -n '/^static void madt_generated_require(/,/^}/p' boot/kernel.c |
    tr '\n' ' ' | tr -s ' ' |
    grep -o 'if (status == MADT_GENERATED_[A-Z_]*) handoff_fail("[a-z0-9-]*")' |
    sed 's/if (status == \(MADT_GENERATED_[A-Z_]*\)) handoff_fail("\([a-z0-9-]*\)")/\1 \2/'
)"
mapfile -t madt_statuses < <(
  sed -n '/^enum madt_generated_status {/,/^};/p' "$madt_admission" |
    grep -o 'MADT_GENERATED_[A-Z_]*' | grep -vx MADT_GENERATED_OK
)
[[ ${#madt_statuses[@]} -gt 0 ]] || {
  echo "error: $madt_admission declares no failure status" >&2; exit 1;
}
for madt_status in "${madt_statuses[@]}"; do
  case "$madt_status" in
    MADT_GENERATED_ENVELOPE_*) madt_reason=topology-madt-generated-envelope ;;
    MADT_GENERATED_ENTRIES_*) madt_reason=topology-madt-generated-entries ;;
    MADT_GENERATED_RESULT_*) madt_reason=topology-admission-result ;;
    *) echo "error: $madt_status belongs to no MADT admission step" >&2; exit 1 ;;
  esac
  [[ "$(grep -c "^$madt_status " <<<"$madt_reasons")" -eq 1 ]] &&
    grep -Fxq "$madt_status $madt_reason" <<<"$madt_reasons" || {
    echo "error: boot_allocate does not map $madt_status to $madt_reason, or maps it more than once" >&2
    exit 1
  }
done
[[ "$(wc -l <<<"$madt_reasons")" -eq ${#madt_statuses[@]} ]] || {
  echo "error: madt_generated_require maps a status the header does not declare" >&2
  exit 1
}
# The frame selection, scrub and publication live in
# include/boot_frame_selection.h (#627): boot_allocate calls its steps in
# order after the MADT admission, keeps the production mutation fixtures
# between them, and maps each status to the reason of its check.
frame_selection=include/boot_frame_selection.h
frame_function() {
  sed -n "/^static inline [a-z_ ]* $1(/,/^}/p" "$frame_selection"
}
for function in boot_frame_terminal boot_frame_select boot_frame_cross_check \
  boot_frame_scrub_selected boot_frame_publication_result \
  boot_frame_publication_check boot_frame_rescan; do
  [[ -n "$(frame_function "$function")" ]] || {
    echo "error: $frame_selection does not define $function" >&2
    exit 1
  }
done
frame_terminal="$(frame_function boot_frame_terminal)"
frame_select="$(frame_function boot_frame_select)"
frame_cross_check="$(frame_function boot_frame_cross_check)"
frame_scrub="$(frame_function boot_frame_scrub_selected)"
frame_publication="$(frame_function boot_frame_publication_result)"
frame_publication_check="$(frame_function boot_frame_publication_check)"
frame_rescan="$(frame_function boot_frame_rescan)"
frame_decoder="$(sed -n '/^static uint32_t boot_frame_decode_candidate(/,/^}/p' boot/kernel.c)"
frame_physical_scrub="$(sed -n '/^static uint32_t boot_frame_physical_scrub(/,/^}/p' boot/kernel.c)"
# check_text TEXT DESCRIPTION REQUIRED...: every required line is in TEXT.
check_text() {
  local text="$1" description="$2" required
  shift 2
  for required in "$@"; do
    grep -Fq "$required" <<<"$text" || {
      echo "error: $description omits $required" >&2
      exit 1
    }
  done
}
# line_in TEXT PATTERN: the line number of the first match of PATTERN.
line_in() {
  grep -n -m1 -F "$2" <<<"$1" | cut -d: -f1
}
# The manifest overlay and the terminal result: three overlay words and one
# free word per block, in block order, then the nine terminal words over the
# free words, checked before the selection.
check_text "$frame_terminal" "the manifest overlay and terminal result" \
  'for (uint64_t block = 0; block < BOOT_FRAME_BLOCKS; ++block) {' \
  'block, BOOT_FRAME_MANIFEST_ARGS(manifest), 1);' \
  'block, BOOT_FRAME_MANIFEST_ARGS(manifest), 2);' \
  'block, BOOT_FRAME_MANIFEST_ARGS(manifest), 3);' \
  'if (status != 1 || error != 0) {' \
  'reserved[block] = mask;' \
  'usable[block], blocked[block], mask);' \
  'for (uint64_t query = 0; query < BOOT_FRAME_TERMINAL_WORDS; ++query)' \
  'terminal[query] = leanos_boot_projection_finish(' \
  'decoded[1], decoded[2], manifest_status, manifest_error,' \
  'decoded[11], decoded[17], 1, query,' \
  'BOOT_FRAME_BITMAP_ARGS(free_words));' \
  'if (terminal[3] >= BOOT_FRAME_COUNT) return BOOT_FRAME_TERMINAL_FRAME;' \
  'if (terminal[5] != decoded[11]) return BOOT_FRAME_TERMINAL_ENTRY_COUNT;'
# The selection: each candidate in order is replayed through the generated
# candidate decoder before its manifest and exact-projection answers, a
# decoder's rejection stops it, and the selected frame is the consumer's
# first acceptance, never the projection's nomination.
check_text "$frame_select" "production selection is not bound to the canonical raw-byte candidate scan:" \
  'for (uint64_t candidate = 0; candidate < BOOT_FRAME_COUNT; ++candidate) {' \
  'uint64_t *state = states[scan];' \
  'const uint32_t status = decode(context, candidate, state);' \
  'return BOOT_FRAME_DECODER;' \
  'candidate, BOOT_FRAME_MANIFEST_ARGS(manifest));' \
  'const uint64_t exact_candidate = leanos_boot_consume_exact_projection(' \
  'BOOT_FRAME_COUNT, candidate, state[1], state[14], state[15],' \
  'if (exact_candidate >= BOOT_FRAME_COUNT) continue;' \
  'first = exact_candidate;' \
  'if (take_next == 0) break;' \
  'second = exact_candidate;'
select_decode_line="$(line_in "$frame_select" 'decode(context, candidate, state)')"
select_rejected_line="$(line_in "$frame_select" 'return BOOT_FRAME_DECODER;')"
select_manifest_line="$(line_in "$frame_select" 'leanos_boot_manifest_candidate(')"
select_consume_line="$(line_in "$frame_select" 'leanos_boot_consume_exact_projection(')"
[[ "$select_decode_line" -lt "$select_rejected_line" &&
   "$select_rejected_line" -lt "$select_manifest_line" &&
   "$select_manifest_line" -lt "$select_consume_line" ]] || {
  echo "error: the selection must decode each candidate and stop at its rejection before asking its manifest and exact projection" >&2
  exit 1
}
if grep -Eq 'terminal|nominat' <<<"$frame_select"; then
  echo "error: production selected a caller-transported projection word" >&2
  exit 1
fi
if grep -Fq 'selected = authority.word[3]' <<<"$production_allocate" ||
   grep -Fq 'frame_budget_physical_frame = authority.word[8]' <<<"$production_allocate"; then
  echo "error: production allocation consumed a caller-transported projection word" >&2
  exit 1
fi
# The cross-check, the scrub, the publication and the rescan.
check_text "$frame_cross_check" "production selected-frame authorization" \
  'if (selected >= BOOT_FRAME_COUNT) return BOOT_FRAME_AUTHORITY_NONE;' \
  'if (terminal[3] != selected) return BOOT_FRAME_AUTHORITY_NOMINATION;' \
  'if (state[16] != selected) return BOOT_FRAME_AUTHORITY_TARGET;' \
  'if (state[11] != decoded[11]) return BOOT_FRAME_AUTHORITY_ENTRY_COUNT;' \
  'if (state[17] != decoded[17]) return BOOT_FRAME_AUTHORITY_HIGHEST;' \
  'if (state[14] != 1) return BOOT_FRAME_AUTHORITY_USABLE;' \
  'if (state[15] != 0) return BOOT_FRAME_AUTHORITY_BLOCKED;' \
  'if (selected_manifest != 1) return BOOT_FRAME_AUTHORITY_MANIFEST;'
check_text "$frame_scrub" "the scrub step" \
  'if (scrub(context, selected) != 1) return BOOT_FRAME_SCRUB;'
check_text "$frame_physical_scrub" "the kernel's physical scrub" \
  'volatile uint8_t *frame = (volatile uint8_t *)(selected * PAGE_BYTES);' \
  'for (uint64_t i = 0; i < PAGE_BYTES; ++i) frame[i] = 0;' \
  'if (frame[i] != 0) return 0;' \
  'return 1;'
[[ "$(line_in "$frame_physical_scrub" 'frame[i] = 0;')" -lt \
   "$(line_in "$frame_physical_scrub" 'if (frame[i] != 0) return 0;')" ]] || {
  echo "error: the kernel's scrub must zero the frame before reading it back" >&2
  exit 1
}
check_text "$frame_publication" "the publication's authority result" \
  'for (uint64_t query = 0; query < BOOT_FRAME_PUBLICATION_WORDS; ++query)' \
  'publication[query] = leanos_boot_authority_result(' \
  'selected, state[16], state[1], state[14], state[15],' \
  'selected_manifest, 1, query);'
check_text "$frame_publication_check" "the publication check" \
  'if (publication[0] != 1) return BOOT_FRAME_PUBLICATION_VERSION;' \
  'if (publication[3] != selected) return BOOT_FRAME_PUBLICATION_FRAME;' \
  'if (publication[4] != selected + 1) return BOOT_FRAME_PUBLICATION_OBJECT;'
check_text "$frame_rescan" "the frame-budget rescan" \
  'if (next >= BOOT_FRAME_COUNT) return BOOT_FRAME_UNPUBLISHED_LIMIT;' \
  'if (next <= published) return BOOT_FRAME_UNPUBLISHED_ORDER;' \
  'const uint32_t status = decode(context, next, state);' \
  'return BOOT_FRAME_DECODER;' \
  'next, BOOT_FRAME_MANIFEST_ARGS(manifest));' \
  'if (state[16] != next) return BOOT_FRAME_RESCAN_TARGET;' \
  'if (state[1] != 1) return BOOT_FRAME_RESCAN_STATUS;' \
  'if (next_manifest != 1) return BOOT_FRAME_RESCAN_MANIFEST;'
[[ "$(line_in "$frame_rescan" 'return BOOT_FRAME_UNPUBLISHED_ORDER;')" -lt \
   "$(line_in "$frame_rescan" 'decode(context, next, state)')" ]] || {
  echo "error: the frame-budget rescan must bound the next frame before decoding it" >&2
  exit 1
}
# The kernel's candidate decoder is the generated decoder over the immutable
# handoff copy (include/boot_handoff_decode.h), and the selection decodes
# from that copy.
check_text "$frame_decoder" "the kernel's candidate decoder" \
  'boot_handoff_decode_candidate(' \
  'handoff->magic, handoff->info_address, handoff->total, candidate,' \
  'handoff->copy, states, &current);' \
  'if (status != BOOT_HANDOFF_OK) return (uint32_t)status;' \
  'load_boot_decode_words(state, states[current]);'
check_text "$production_allocate" "production allocation's frame selection" \
  '.bytes = boot_handoff_copy,' \
  'const uint8_t *info = handoff.bytes;' \
  'const uint64_t manifest[BOOT_FRAME_MANIFEST_WORDS] = {' \
  'BOOT_MANIFEST_ARGS(info_address, total)' \
  'manifest, decoded.word, boot_projection_usable,' \
  'boot_projection_blocked, boot_projection_reserved, authority.word), 0);' \
  '.copy = (const uint64_t *)info' \
  'uint64_t *const selected_authority = selection_states[0];' \
  'boot_frame_decode_candidate, &candidates, manifest,' \
  'BOOT_FRAME_TAKE_NEXT, selection_states, &selected,' \
  'boot_frame_require(selection, decoder_status);' \
  'authority.word, decoded.word, selected, selected_authority,' \
  'boot_frame_physical_scrub, 0, selected), 0);' \
  'boot_frame_publication_result(selected, selected_authority,' \
  'selected, publication.word), 0);' \
  'published_boot_object = publication.word[4];' \
  'frame_budget_boot_published_frame = selected;' \
  'frame_budget_physical_frame = next_selected;' \
  'boot_frame_decode_candidate, &candidates, manifest, decoded.word,' \
  'frame_budget_boot_published_frame, frame_budget_physical_frame,' \
  'selection_states[1], frame_budget_rescan, &decoder_status);' \
  'boot_frame_require(rescan, decoder_status);'
[[ "$(grep -c 'define BOOT_FRAME_TAKE_NEXT' boot/kernel.c)" -eq 2 &&
   "$(grep -B1 -A3 -x '#define BOOT_FRAME_TAKE_NEXT 1u' boot/kernel.c | tr '\n' '|')" == \
   '#ifdef LEANOS_FRAME_BUDGET_SCENARIO|#define BOOT_FRAME_TAKE_NEXT 1u|#else|#define BOOT_FRAME_TAKE_NEXT 0u|#endif|' ]] || {
  echo "error: only the frame-budget scenario takes the next accepted frame" >&2
  exit 1
}
# The order of boot_allocate's steps, with the mutation fixtures between them.
terminal_line="$(line_in "$production_allocate" 'boot_frame_require(boot_frame_terminal(')"
select_line="$(line_in "$production_allocate" 'boot_frame_select(')"
selection_required_line="$(line_in "$production_allocate" 'boot_frame_require(selection, decoder_status);')"
cross_line="$(line_in "$production_allocate" 'boot_frame_require(boot_frame_cross_check(')"
publication_line="$(line_in "$production_allocate" 'boot_frame_publication_result(')"
publication_check_line="$(line_in "$production_allocate" 'boot_frame_require(boot_frame_publication_check(')"
published_line="$(line_in "$production_allocate" 'published_boot_object = publication.word[4];')"
rescan_line="$(line_in "$production_allocate" 'boot_frame_rescan(')"
handoff_record_line="$(line_in "$production_allocate" 'LEANOS_SERIAL_7_HANDOFF')"
for line in terminal_line select_line selection_required_line cross_line \
  scrub_line publication_line publication_check_line published_line \
  rescan_line handoff_record_line; do
  [[ -n "${!line}" ]] || { echo "error: production allocation lacks its $line" >&2; exit 1; }
done
[[ "$madt_line" -lt "$terminal_line" && "$terminal_line" -lt "$select_line" &&
   "$select_line" -lt "$selection_required_line" &&
   "$selection_required_line" -lt "$cross_line" && "$cross_line" -lt "$scrub_line" &&
   "$scrub_line" -lt "$publication_line" &&
   "$publication_line" -lt "$publication_check_line" &&
   "$publication_check_line" -lt "$published_line" &&
   "$published_line" -lt "$rescan_line" && "$rescan_line" -lt "$handoff_record_line" ]] || {
  echo "error: production must overlay and finish the projection, select, cross-check, scrub, then publish, then rescan, after the MADT admission" >&2
  exit 1
}
for required in \
  'LEANOS_PROJECTION_SELECTION_MUTATION_FIXTURE' \
  'const uint64_t exact_replay_selected = selected' \
  'authority.word[3] = selected == 4095 ? selected - 1 : selected + 1' \
  'selected != exact_replay_selected' \
  'handoff_fail("projection-mutation-raw-selection")' \
  'LEANOS_RAW_SELECTION_MUTATION_FIXTURE' \
  'LEANOS_RAW_CLASSIFICATION_MUTATION_FIXTURE' \
  'LEANOS_PUBLICATION_RESULT_MUTATION_FIXTURE' \
  'publication.word[3] = selected == 4095 ? selected - 1 : selected + 1'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production mutation fixtures omit $required" >&2
    exit 1
  }
done
mutation_line="$(grep -n 'authority.word\[3\] = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
raw_selection_mutation_line="$(grep -n '^    selected = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
raw_classification_mutation_line="$(grep -n 'selected_authority\[14\] = 0' <<<"$production_allocate" | cut -d: -f1)"
publication_mutation_line="$(grep -n 'publication.word\[3\] = selected == 4095' <<<"$production_allocate" | cut -d: -f1)"
for line in mutation_line raw_selection_mutation_line \
  raw_classification_mutation_line publication_mutation_line; do
  [[ -n "${!line}" ]] || { echo "error: production allocation lacks its $line" >&2; exit 1; }
done
if (( mutation_line <= selection_required_line || mutation_line >= cross_line ||
      raw_selection_mutation_line <= selection_required_line ||
      raw_selection_mutation_line >= cross_line ||
      raw_classification_mutation_line <= selection_required_line ||
      raw_classification_mutation_line >= cross_line )); then
  echo "error: the selection mutation fixtures must sit between the selection and its cross-check, before scrub/publication" >&2
  exit 1
fi
if (( publication_mutation_line <= publication_line ||
      publication_mutation_line >= publication_check_line )); then
  echo "error: the publication mutation fixture must sit between the authority result and its check" >&2
  exit 1
fi
if grep -Eq 'leanos_boot_(projection_manifest|projection_free|projection_finish|manifest_candidate|consume_exact_projection|authority_result)\(' \
    <<<"$production_allocate"; then
  echo "error: production allocation asks a frame-selection export itself instead of through $frame_selection" >&2
  exit 1
fi
# boot_frame_require, one line per status: "status reason".  The cross-check
# takes its fixture's reason, and a decoder's rejection the reason of the
# decoder's own status.
frame_require="$(
  sed -n '/^static inline __attribute__((always_inline)) void boot_frame_require(/,/^}/p' boot/kernel.c |
    tr '\n' ' ' | tr -s ' '
)"
frame_reasons="$(
  grep -o 'if (status == BOOT_FRAME_[A-Z_]*) handoff_fail(\("[a-z0-9-]*"\|BOOT_FRAME_AUTHORITY_REASON\))' <<<"$frame_require" |
    sed 's/if (status == \(BOOT_FRAME_[A-Z_]*\)) handoff_fail(\(.*\))/\1 \2/' |
    sed 's/ BOOT_FRAME_AUTHORITY_REASON$/ projection-authority/; s/ "\(.*\)"$/ \1/'
)"
[[ "$(grep -c 'define BOOT_FRAME_AUTHORITY_REASON' boot/kernel.c)" -eq 2 &&
   "$(grep -B1 -A3 -x '#define BOOT_FRAME_AUTHORITY_REASON "raw-selection-authority"' boot/kernel.c | tr '\n' '|')" == \
   '#ifdef LEANOS_RAW_SELECTION_MUTATION_FIXTURE|#define BOOT_FRAME_AUTHORITY_REASON "raw-selection-authority"|#else|#define BOOT_FRAME_AUTHORITY_REASON "projection-authority"|#endif|' ]] || {
  echo "error: the cross-check's reason is not projection-authority, or raw-selection-authority under its fixture" >&2
  exit 1
}
grep -Fq 'if (status == BOOT_FRAME_DECODER) boot_handoff_require((enum boot_handoff_status)decoder_status);' \
    <<<"$frame_require" || {
  echo "error: boot_frame_require does not give a decoder's rejection the decoder's own reason" >&2
  exit 1
}
mapfile -t frame_statuses < <(
  sed -n '/^enum boot_frame_status {/,/^};/p' "$frame_selection" |
    grep -o 'BOOT_FRAME_[A-Z_]*' | grep -vx BOOT_FRAME_OK
)
[[ ${#frame_statuses[@]} -gt 0 ]] || {
  echo "error: $frame_selection declares no failure status" >&2; exit 1;
}
for frame_status in "${frame_statuses[@]}"; do
  case "$frame_status" in
    BOOT_FRAME_TERMINAL_*) frame_reason=projection-terminal ;;
    BOOT_FRAME_DECODER) frame_reason=authority-rejected ;;
    BOOT_FRAME_AUTHORITY_*) frame_reason=projection-authority ;;
    BOOT_FRAME_SCRUB) frame_reason=scrub ;;
    BOOT_FRAME_PUBLICATION_*) frame_reason=publication ;;
    BOOT_FRAME_UNPUBLISHED_*) frame_reason=frame-budget-unpublished-frame ;;
    BOOT_FRAME_RESCAN_*) frame_reason=frame-budget-projection-authority ;;
    *) echo "error: $frame_status belongs to no frame-selection check" >&2; exit 1 ;;
  esac
  [[ "$(grep -c "^$frame_status " <<<"$frame_reasons")" -eq 1 ]] &&
    grep -Fxq "$frame_status $frame_reason" <<<"$frame_reasons" || {
    echo "error: boot_allocate does not map $frame_status to $frame_reason, or maps it more than once" >&2
    exit 1
  }
done
[[ "$(wc -l <<<"$frame_reasons")" -eq ${#frame_statuses[@]} ]] || {
  echo "error: boot_frame_require maps a status the header does not declare" >&2
  exit 1
}
if grep -Eq 'mb2_(tag|mmap)|boot_frames|reserve_byte_range|allocation_check' \
    <<<"$production_allocate$(cat "$frame_selection")"; then
  echo "error: production allocation retained a C handoff policy authority" >&2
  exit 1
fi
# The candidate decoder accepts a candidate only as its own target frame.
for required in 'states[0][16] != candidate' 'states[at][16] != candidate'; do
  grep -Fq "$required" <<<"$production_authority" || {
    echo "error: production selected-frame authorization omits $required" >&2
    exit 1
  }
done
grep -Fq 'struct boot_decode_state { uint64_t word[41]; };' boot/kernel.c &&
  grep -Fxq '#define BOOT_DECODE_WORDS 41' "$handoff_decode" || {
  echo "error: production decoder does not retain parser, typed entry, and ACPI root state" >&2
  exit 1
}
for required in 'query < BOOT_DECODE_WORDS' 'state[18], state[23],' \
  'state[38],' 'info_address, offset, chunk, terminal, query' \
  'leanos_boot_decode_step_v5('; do
  grep -Fq "$required" <<<"$production_transition" || {
    echo "error: production decoder omits scalar ABI v5 ACPI-root state: $required" >&2
    exit 1
  }
done
for required in 'states[0][0] != 5' 'states[0][16] != 0' 'states[0][30] != 0' \
  'boot_decode_transition(states[at], info_address, offset,' \
  'info[offset / 8], terminal, states[1u - at]);' 'at = 1u - at;' \
  'if (state[2] != 0) break;' 'if (state[19] == 1) {' \
  'state[11] > BOOT_PROJECTION_ENTRIES' \
  'projection->record(projection->context, state[11] - 1, state[20],' \
  'leanos_boot_projection_entry(' \
  'projection->usable[block], projection->blocked[block], 4);' \
  'return BOOT_HANDOFF_DECODE_INCOMPLETE_PHASE;'; do
  grep -Fq "$required" <<<"$production_decode" || {
    echo "error: the production projection omits $required" >&2
    exit 1
  }
done
for required in 'boot_decode_transition(states[at], info_address, offset,' \
  'if (states[at][2] != 0) break;' \
  'return BOOT_HANDOFF_AUTHORITY_REJECTED_TARGET;'; do
  grep -Fq "$required" <<<"$production_authority" || {
    echo "error: the production candidate authority omits $required" >&2
    exit 1
  }
done
# The extent: the magic and the address are checked before total_size is
# read, through the kernel's identity-mapped read, and its bounds after.
for required in \
  'if (magic != BOOT_HANDOFF_MULTIBOOT2_MAGIC) return BOOT_HANDOFF_MAGIC;' \
  'if ((info_address & 7u) != 0) return BOOT_HANDOFF_POINTER_ALIGNMENT;' \
  'if (info_address < BOOT_HANDOFF_PAGE_BYTES) return BOOT_HANDOFF_POINTER_LOW;' \
  'if (info_address >= BOOT_HANDOFF_ACCESSIBLE_LIMIT)' \
  'const uint32_t size = (uint32_t)read(context, info_address);' \
  'if (size < 16u) return BOOT_HANDOFF_BOUNDS_SMALL;' \
  'if (size > BOOT_HANDOFF_MAX_BYTES) return BOOT_HANDOFF_BOUNDS_LARGE;' \
  'if ((size & 7u) != 0) return BOOT_HANDOFF_BOUNDS_ALIGNMENT;' \
  'if (size > BOOT_HANDOFF_ACCESSIBLE_LIMIT - info_address)'; do
  grep -Fq "$required" <<<"$production_extent" || {
    echo "error: the production handoff extent omits $required" >&2
    exit 1
  }
done
pointer_line="$(grep -n 'info_address >= BOOT_HANDOFF_ACCESSIBLE_LIMIT' <<<"$production_extent" | cut -d: -f1)"
size_line="$(grep -n 'read(context, info_address)' <<<"$production_extent" | cut -d: -f1)"
bounds_line="$(grep -n 'size > BOOT_HANDOFF_ACCESSIBLE_LIMIT - info_address' <<<"$production_extent" | cut -d: -f1)"
[[ "$(grep -c 'read(' <<<"$production_extent")" -eq 1 && -n "$pointer_line" &&
   "$pointer_line" -lt "$size_line" && "$size_line" -lt "$bounds_line" ]] || {
  echo "error: the handoff extent must check the address before reading total_size once" >&2
  exit 1
}
grep -Fq 'uint64_t word = *(const uint64_t *)(uintptr_t)physical_address;' \
    <<<"$production_handoff_read" &&
  grep -Fq 'if (physical_address == *(const uint32_t *)context) word |= 1ull << 32;' \
    <<<"$production_handoff_read" || {
  echo "error: the handoff's physical read is not the identity-mapped load with its malformed-handoff fixture" >&2
  exit 1
}
# The copy: each chunk is read once and replayed through the generated
# stream, and enters the copy only once every word of its transition is
# accepted.
for required in \
  'leanos_boot_handoff_stream_init(' \
  'magic, info_address, total, info_address, query);' \
  'const uint64_t chunk = read(context, (uint64_t)info_address + offset);' \
  'leanos_boot_handoff_stream_step(' \
  'state[6], info_address, offset, 8, chunk, terminal, query);' \
  'if (answer[5] != offset + 8) return BOOT_HANDOFF_STREAM_STEP_OFFSET;' \
  'if (answer[8] != 8) return BOOT_HANDOFF_STREAM_STEP_COUNT;' \
  'if (answer[7] != chunk) return BOOT_HANDOFF_STREAM_STEP_EXPOSED;' \
  'if (answer[1] != (terminal ? 1u : 0u))' \
  'copy[offset / 8] = answer[7];' \
  'if (state[5] != total) return BOOT_HANDOFF_STREAM_INCOMPLETE_OFFSET;'; do
  grep -Fq "$required" <<<"$production_handoff_copy" || {
    echo "error: the production handoff copy omits generated stream binding: $required" >&2
    exit 1
  }
done
status_check_line="$(grep -n 'return BOOT_HANDOFF_STREAM_STEP_STATUS;' <<<"$production_handoff_copy" | cut -d: -f1)"
store_line="$(grep -n 'copy\[offset / 8\] = answer\[7\];' <<<"$production_handoff_copy" | cut -d: -f1)"
[[ "$(grep -c 'read(' <<<"$production_handoff_copy")" -eq 1 &&
   -n "$status_check_line" && "$status_check_line" -lt "$store_line" ]] || {
  echo "error: the handoff copy must read each chunk once and store it only after its transition is accepted" >&2
  exit 1
}
# boot_handoff_project: the copy, its length, the projection, then the
# decoder's acceptance.
project_copy_line="$(grep -n 'boot_handoff_stream_copy(' <<<"$production_project" | cut -d: -f1)"
project_length_line="$(grep -n 'if (length != total) return BOOT_HANDOFF_COPY_LENGTH;' <<<"$production_project" | cut -d: -f1)"
project_decode_line="$(grep -n 'boot_handoff_decode_projection(' <<<"$production_project" | cut -d: -f1)"
project_rejected_line="$(grep -n 'return BOOT_HANDOFF_DECODE_REJECTED_ERROR;' <<<"$production_project" | cut -d: -f1)"
[[ -n "$project_copy_line" && -n "$project_length_line" &&
   -n "$project_decode_line" && -n "$project_rejected_line" &&
   "$project_copy_line" -lt "$project_length_line" &&
   "$project_length_line" -lt "$project_decode_line" &&
   "$project_decode_line" -lt "$project_rejected_line" ]] &&
  grep -Fq 'magic, info_address, total, copy, projection, states, &decoded);' \
    <<<"$production_project" || {
  echo "error: boot_handoff_project must copy, check the length, decode the copy, then require acceptance" >&2
  exit 1
}
# boot_allocate: the extent, the APIC observation, the copy and projection,
# all before the ACPI copy, through the kernel's read and storage.
for required in \
  'boot_handoff_require(boot_handoff_extent(' \
  'boot_handoff_physical_read, &info_address, magic, info_address,' \
  'const uint32_t executing_apic_id = observe_executing_apic_id();' \
  'total, (uint64_t *)boot_handoff_copy, &boot_projection,' \
  'load_boot_decode_state(&decoded, decode_states[decoded_state]);'; do
  grep -Fq "$required" <<<"$production_allocate" || {
    echo "error: production allocation omits the handoff header's sequence: $required" >&2
    exit 1
  }
done
extent_line="$(grep -n 'boot_handoff_require(boot_handoff_extent(' <<<"$production_allocate" | cut -d: -f1)"
apic_line="$(grep -n 'observe_executing_apic_id()' <<<"$production_allocate" | cut -d: -f1)"
project_line="$(grep -n 'boot_handoff_require(boot_handoff_project(' <<<"$production_allocate" | cut -d: -f1)"
acpi_line="$(grep -n 'acpi_table_copy_require(acpi_copy_root_and_tables(' <<<"$production_allocate" | cut -d: -f1)"
[[ -n "$extent_line" && -n "$apic_line" && -n "$project_line" && -n "$acpi_line" &&
   "$extent_line" -lt "$apic_line" && "$apic_line" -lt "$project_line" &&
   "$project_line" -lt "$acpi_line" ]] || {
  echo "error: production must check the extent, observe the APIC ID, then copy and decode the handoff before the ACPI copy" >&2
  exit 1
}
# The projection's entries go to the kernel's bounded table.
grep -Fq 'boot_projection_entries[slot].kind = kind;' \
    <<<"$(sed -n '/^static void boot_projection_record_entry(/,/^}/p' boot/kernel.c)" &&
  grep -Fq '.record = boot_projection_record_entry,' boot/kernel.c || {
  echo "error: the projection's entries are not recorded in boot_projection_entries" >&2
  exit 1
}
# boot_handoff_require, one line per status: "status reason".  Each status
# takes the reason of the check it splits.
handoff_reasons="$(
  sed -n '/^static inline __attribute__((always_inline)) void boot_handoff_require(/,/^}/p' boot/kernel.c |
    tr '\n' ' ' | tr -s ' ' |
    grep -o 'if (status == BOOT_HANDOFF_[A-Z_]*) handoff_fail("[a-z0-9-]*")' |
    sed 's/if (status == \(BOOT_HANDOFF_[A-Z_]*\)) handoff_fail("\([a-z0-9-]*\)")/\1 \2/'
)"
mapfile -t handoff_statuses < <(
  sed -n '/^enum boot_handoff_status {/,/^};/p' "$handoff_decode" |
    grep -o 'BOOT_HANDOFF_[A-Z_]*' | grep -vx BOOT_HANDOFF_OK
)
[[ ${#handoff_statuses[@]} -gt 0 ]] || {
  echo "error: $handoff_decode declares no failure status" >&2; exit 1;
}
for handoff_status in "${handoff_statuses[@]}"; do
  case "$handoff_status" in
    BOOT_HANDOFF_MAGIC) handoff_reason=magic ;;
    BOOT_HANDOFF_POINTER_*) handoff_reason=pointer ;;
    BOOT_HANDOFF_BOUNDS_*) handoff_reason=bounds ;;
    BOOT_HANDOFF_STREAM_INIT_*) handoff_reason=stream-init ;;
    BOOT_HANDOFF_STREAM_STEP_*) handoff_reason=stream-step ;;
    BOOT_HANDOFF_STREAM_INCOMPLETE_*) handoff_reason=stream-incomplete ;;
    BOOT_HANDOFF_COPY_LENGTH) handoff_reason=topology-handoff-length ;;
    BOOT_HANDOFF_DECODE_INIT_*) handoff_reason=decode-init ;;
    BOOT_HANDOFF_PROJECTION_COUNT_*) handoff_reason=projection-entry-count ;;
    BOOT_HANDOFF_PROJECTION_ENTRY_*) handoff_reason=projection-entry ;;
    BOOT_HANDOFF_DECODE_INCOMPLETE_*) handoff_reason=decode-incomplete ;;
    BOOT_HANDOFF_DECODE_REJECTED_*) handoff_reason=decode-rejected ;;
    BOOT_HANDOFF_AUTHORITY_INIT_*) handoff_reason=authority-init ;;
    BOOT_HANDOFF_AUTHORITY_REJECTED_*) handoff_reason=authority-rejected ;;
    *) echo "error: $handoff_status belongs to no handoff check" >&2; exit 1 ;;
  esac
  [[ "$(grep -c "^$handoff_status " <<<"$handoff_reasons")" -eq 1 ]] &&
    grep -Fxq "$handoff_status $handoff_reason" <<<"$handoff_reasons" || {
    echo "error: boot_allocate does not map $handoff_status to $handoff_reason, or maps it more than once" >&2
    exit 1
  }
done
[[ "$(wc -l <<<"$handoff_reasons")" -eq ${#handoff_statuses[@]} ]] || {
  echo "error: boot_handoff_require maps a status the header does not declare" >&2
  exit 1
}
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
generated="build/boundary-abi"
./scripts/generate-oracle.sh "$generated"

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
    -I"$generated" -c "$harness" -o "$build/host.o"
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
"$cc" "${cflags[@]}" -I"$generated" \
  -c tests/boot-handoff-stream-freestanding.c -o "$build/test.o"
"$cc" -m64 -std=c11 -O2 -Wall -Wextra -Werror \
  -DLEANOS_HOSTED_REPLAY=1 -I"$generated" \
  -c tests/boot-handoff-stream-freestanding.c -o "$build/host.o"
"$cc" -m64 -nostdlib -static -no-pie -Wl,--gc-sections -Wl,-e,_start \
  "$build/test.o" "$build/stream.o" "$build/authority.o" -o "$build/stream.elf"
"$cc" -m64 -no-pie -Wl,--gc-sections \
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
    _start|check_stream|decode|decode_entry_count|decode_extent|decode_v5_extent|expect_decode_error|memcpy|memset|step_query|\
leanos_boot_handoff_stream_init|\
leanos_boot_handoff_stream_step|\
leanos_boot_decode_init|leanos_boot_decode_step|\
leanos_boot_decode_init_v5|leanos_boot_decode_step_v5|leanos_boot_manifest_candidate|\
leanos_boot_manifest_start|\
leanos_boot_consume_exact_projection|leanos_boot_publish_authority|\
leanos_boot_authority_result|\
leanos_boot_projection_entry|leanos_boot_projection_manifest|\
leanos_boot_projection_free|leanos_boot_projection_finish|\
lp_leanos___private_LeanOS_BootMemoryMapStreaming_0__LeanOS_BootMemoryMapStreaming_canonicalChunk|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_manifestValid|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_acpiRootStepWord|\
lp_leanos_LeanOS_BootMemoryMapStreamAuthority_acpiTagStepWord|\
lp_leanos___private_LeanOS_BootMemoryMapStreamAuthority_0__LeanOS_BootMemoryMapStreamAuthority_byteAt|\
lp_leanos___private_LeanOS_BootMemoryMapStreamAuthority_0__LeanOS_BootMemoryMapStreamAuthority_sumWord4|\
lp_leanos___private_LeanOS_BootMemoryMapStreamAuthority_0__LeanOS_BootMemoryMapStreamAuthority_sumWord8|\
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
