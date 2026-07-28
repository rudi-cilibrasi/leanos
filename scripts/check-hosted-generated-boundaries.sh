#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-ordinary}"
manifest=scripts/hosted-generated-boundaries.tsv
source scripts/hosted-boundary-harness-scan.sh

case "$mode" in
  ordinary|sanitized) ;;
  *)
    echo "usage: $0 [ordinary|sanitized]" >&2
    exit 2
    ;;
esac

# Fail before compiling if image construction introduces a generated module
# without assigning it to a hosted boundary. BootAllocation is the one retired
# exception: the focused freestanding final-ELF gate below requires its legacy
# exported adapter to be absent.
declare -A manifest_ids=()
declare -A manifest_modules=()
declare -A manifest_exports=()
declare -A all_source_exports=()
while IFS=$'\t' read -r id runner harness generation target modules exports assertion; do
  [[ -n "$id" && "${id:0:1}" != "#" ]] || continue
  [[ -z "${manifest_ids[$id]+x}" ]] || {
    echo "error: duplicate hosted generated-boundary id '$id'" >&2
    exit 1
  }
  manifest_ids["$id"]=1
  IFS=',' read -ra module_specs <<<"$modules"
  for spec in "${module_specs[@]}"; do
    module="${spec%%=*}"
    [[ -n "$module" ]] || {
      echo "error: hosted boundary '$id' has an empty module entry" >&2
      exit 1
    }
    manifest_modules["$module"]=1
  done
  declare -A row_exports=()
  declare -A source_exports=()
  IFS=',' read -ra export_specs <<<"$exports"
  for symbol in "${export_specs[@]}"; do
    [[ -n "$symbol" ]] || {
      echo "error: hosted boundary '$id' has an empty export entry" >&2
      exit 1
    }
    [[ -z "${row_exports[$symbol]+x}" ]] || {
      echo "error: hosted boundary '$id' repeats export '$symbol'" >&2
      exit 1
    }
    row_exports["$symbol"]=1
    manifest_exports["$symbol"]=1
  done
  for spec in "${module_specs[@]}"; do
    source="${spec#*=}"
    [[ "$source" != "$spec" ]] || source="LeanOS/$spec.lean"
    [[ -f "$source" ]] || continue
    while IFS= read -r symbol; do
      [[ -z "${source_exports[$symbol]+x}" ]] || {
        echo "error: hosted boundary '$id' has duplicate source export '$symbol'" >&2
        exit 1
      }
      source_exports["$symbol"]=1
      all_source_exports["$symbol"]=1
    done < <(sed -n 's/^[[:space:]]*@\[export \([^]]*\)\].*/\1/p' "$source")
  done
  for symbol in "${export_specs[@]}"; do
    [[ -n "${source_exports[$symbol]+x}" ]] || {
      echo "error: hosted boundary '$id' inventories stale export '$symbol'" >&2
      exit 1
    }
    if ! leanos_harness_calls_export "$harness" "$symbol"; then
      echo "error: hosted boundary '$id' export '$symbol' is absent from its own harness" >&2
      exit 1
    fi
  done
done <"$manifest"

# BootAllocation is retired from the image's generated-object inventory, but
# keep its exception export-specific so another adapter cannot hide behind the
# module-wide exclusion below.
declare -A retired_boot_allocation_exports=(
  [leanos_boot_allocation_check]=1
)
declare -A observed_boot_allocation_exports=()
while IFS= read -r symbol; do
  observed_boot_allocation_exports["$symbol"]=1
  [[ -n "${retired_boot_allocation_exports[$symbol]+x}" ]] || {
    echo "error: BootAllocation introduces untracked export '$symbol'" >&2
    exit 1
  }
done < <(
  sed -n 's/^[[:space:]]*@\[export \([^]]*\)\].*/\1/p' \
    LeanOS/BootAllocation.lean
)
for symbol in "${!retired_boot_allocation_exports[@]}"; do
  [[ -n "${observed_boot_allocation_exports[$symbol]+x}" ]] || {
    echo "error: retired BootAllocation export '$symbol' is missing" >&2
    exit 1
  }
done

for symbol in "${!all_source_exports[@]}"; do
  [[ -n "${manifest_exports[$symbol]+x}" ]] || {
    echo "error: generated source export '$symbol' is absent from $manifest" >&2
    exit 1
  }
done

while IFS= read -r source; do
  module="${source#LeanOS/}"
  module="${module%.lean}"
  [[ "$module" == BootAllocation ]] && continue
  [[ -n "${manifest_modules[$module]+x}" ]] || {
    echo "error: boot-reachable generated module '$module' is absent from $manifest" >&2
    exit 1
  }
done < <(
  sed -n 's#.*\(LeanOS/[A-Za-z0-9_/]*\.lean\).*#\1#p' \
    scripts/build-image.sh | sort -u
)

boundaries=0
evidence=build/hosted-sanitizer-evidence
if [[ "$mode" == sanitized ]]; then
  mkdir -p "$evidence"
  : >"$evidence/first-failing-boundary.txt"
fi
while IFS=$'\t' read -r id runner harness generation target modules exports assertion; do
  [[ -n "$id" && "${id:0:1}" != "#" ]] || continue
  for path in "$runner" "$harness"; do
    [[ -f "$path" ]] || {
      echo "error: hosted boundary '$id' inventories missing path $path" >&2
      exit 1
    }
  done
  case "$generation" in
    direct|lake-ir) ;;
    *)
      echo "error: hosted boundary '$id' has unknown generation mode '$generation'" >&2
      exit 1
      ;;
  esac
  [[ -n "$modules" && -n "$exports" && -n "$assertion" ]] || {
    echo "error: hosted boundary '$id' has an incomplete manifest row" >&2
    exit 1
  }
  if [[ "$mode" == sanitized ]]; then
    log="$evidence/$id.log"
    if ! LEANOS_HOSTED_BOUNDARY_ID="$id" "$runner" "$mode" \
        >"$log" 2>&1; then
      printf '%s\n' "$id" >"$evidence/first-failing-boundary.txt"
      cat "$log" >&2
      exit 1
    fi
    cat "$log"
  else
    LEANOS_HOSTED_BOUNDARY_ID="$id" "$runner" "$mode"
  fi
  boundaries=$((boundaries + 1))
done < "$manifest"

[[ "$boundaries" -gt 0 ]] || {
  echo "error: hosted generated-boundary manifest is empty" >&2
  exit 1
}
if [[ "$mode" == sanitized ]]; then
  source scripts/hosted-sanitizer-config.sh
  leanos_assert_pinned_toolchain
  {
    printf 'source-revision: '
    git rev-parse HEAD
    "$leanos_host_cc" --version | head -n 1
    printf 'compiler-package: gcc-13=%s\n' \
      "$(dpkg-query -W -f='${Version}' gcc-13)"
    printf 'asan-package: libasan8=%s\n' \
      "$(dpkg-query -W -f='${Version}' libasan8)"
    printf 'ubsan-package: libubsan1=%s\n' \
      "$(dpkg-query -W -f='${Version}' libubsan1)"
    printf 'compile-flags:'
    printf ' %q' "${leanos_host_sanitizer_flags[@]}"
    printf '\nASAN_OPTIONS=%s\nUBSAN_OPTIONS=%s\n' \
      "$leanos_host_asan_options" "$leanos_host_ubsan_options"
  } >"$evidence/configuration.txt"
fi
echo "Hosted generated-boundary $mode replay passed ($boundaries boundaries)"
