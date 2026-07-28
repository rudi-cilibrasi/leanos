#!/usr/bin/env bash

leanos_prepare_boundary_coverage() {
  local build="$1"
  local exports="$2"
  local source="$build/boundary-coverage.c"
  local expected="$build/boundary-coverage.expected"
  : >"$expected"
  {
    printf '%s\n' \
      '#include <stdio.h>' \
      '#include <stdlib.h>'
    IFS=',' read -ra symbols <<<"$exports"
    for symbol in "${symbols[@]}"; do
      printf '%s\n' "$symbol" >>"$expected"
    done
    printf '%s\n' \
      'struct target { void *address; const char *name; unsigned char hit; };' \
      'static struct target targets[] = {'
    for symbol in "${symbols[@]}"; do
      printf '  { NULL, "%s", 0 },\n' "$symbol"
    done
    printf '%s\n' \
      '};' \
      'void leanos_register_boundary_target(const char *, void *) __attribute__((no_instrument_function));' \
      'void leanos_register_boundary_target(const char *name, void *address) {' \
      '  for (unsigned i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i) {' \
      '    if (__builtin_strcmp(targets[i].name, name) != 0) continue;' \
      '    targets[i].address = address;' \
      '    return;' \
      '  }' \
      '  fprintf(stderr, "error: unmanifested hosted boundary target %s\n", name);' \
      '  exit(1);' \
      '}' \
      'void __cyg_profile_func_enter(void *, void *) __attribute__((no_instrument_function));' \
      'void __cyg_profile_func_exit(void *, void *) __attribute__((no_instrument_function));' \
      'void __cyg_profile_func_enter(void *fn, void *caller) {' \
      '  (void)caller;' \
      '  for (unsigned i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i)' \
      '    if (targets[i].address == fn) targets[i].hit = 1;' \
      '}' \
      'void __cyg_profile_func_exit(void *fn, void *caller) { (void)fn; (void)caller; }' \
      'static void write_coverage(void) __attribute__((destructor, no_instrument_function));' \
      'static void write_coverage(void) {' \
      '  const char *path = getenv("LEANOS_BOUNDARY_COVERAGE_FILE");' \
      '  if (path == NULL) return;' \
      '  FILE *file = fopen(path, "w");' \
      '  if (file == NULL) return;' \
      '  for (unsigned i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i)' \
      '    if (targets[i].hit) fprintf(file, "%s\n", targets[i].name);' \
      '  fclose(file);' \
      '}'
  } >"$source"
  sort -o "$expected" "$expected"
}

leanos_check_boundary_coverage() {
  local build="$1"
  local actual="$build/boundary-coverage.actual"
  [[ -f "$actual" ]] || {
    echo "error: hosted boundary produced no runtime function-entry coverage" >&2
    return 1
  }
  sort -o "$actual" "$actual"
  if ! cmp -s "$build/boundary-coverage.expected" "$actual"; then
    echo "error: hosted boundary did not execute every row export" >&2
    diff -u "$build/boundary-coverage.expected" "$actual" >&2 || true
    return 1
  fi
}
