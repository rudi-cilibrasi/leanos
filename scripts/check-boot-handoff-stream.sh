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
  leanos_boot_projection_manifest \
  leanos_boot_projection_free projection_finish_query \
  decode_boot_candidate_authority leanos_boot_manifest_candidate \
  leanos_boot_consume_exact_projection leanos_boot_authority_result \
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
scrub_line="$(grep -n 'frame\[i\] = 0' <<<"$production_allocate" | cut -d: -f1)"
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
for required in 'states[0][16] != candidate' 'states[at][16] != candidate' \
  'decode_boot_candidate_authority(' \
  'candidate_authority.word[14]' 'candidate_authority.word[15]' \
  'selected_authority.word[14] != 1' \
  'selected_authority.word[15] != 0'; do
  grep -Fq "$required" <<<"$production_allocate$production_authority" || {
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
