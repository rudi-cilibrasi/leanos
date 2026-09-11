/* Replay the native combined BSP/topology candidate through generated C. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS 1
#include "boundary-abi.h"
extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_QotomBootstrapABI(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define MAX_LINE 16384

static lean_object *read_byte_array(const char *path) {
  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    fprintf(stderr, "firmware corpus: cannot open %s\n", path);
    exit(1);
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    fprintf(stderr, "firmware corpus: cannot size %s\n", path);
    exit(1);
  }
  long size = ftell(file);
  if (size < 0 || size > 1048576) {
    fprintf(stderr, "firmware corpus: %s has an unusable size\n", path);
    exit(1);
  }
  rewind(file);
  lean_object *bytes = lean_alloc_sarray(1, (size_t)size, (size_t)size);
  if (size > 0 &&
      fread(lean_sarray_cptr(bytes), 1, (size_t)size, file) != (size_t)size) {
    fprintf(stderr, "firmware corpus: short read of %s\n", path);
    exit(1);
  }
  fclose(file);
  return bytes;
}

static uint64_t parse_u64(const char *text, const char *what) {
  char *end = NULL;
  unsigned long long value = strtoull(text, &end, 10);
  if (end == text || (*end != '\0' && *end != '\n')) {
    fprintf(stderr, "firmware corpus: malformed %s '%s'\n", what, text);
    exit(1);
  }
  return (uint64_t)value;
}

static char *next_field(char **cursor) {
  char *start = *cursor;
  if (start == NULL) {
    return NULL;
  }
  char *tab = strchr(start, '\t');
  if (tab != NULL) {
    *tab = '\0';
    *cursor = tab + 1;
  } else {
    *cursor = NULL;
  }
  return start;
}

struct root_bundle {
  uint64_t address, magic, info_address;
  lean_object *info, *root, *addresses, *tables;
};

static struct root_bundle read_root_bundle(const char *path) {
  FILE *file = fopen(path, "r");
  if (!file) { fprintf(stderr, "firmware corpus: cannot open root bundle %s\n", path); exit(1); }
  char line[MAX_LINE];
  if (!fgets(line, sizeof(line), file) || !strchr(line, '\n')) {
    fprintf(stderr, "firmware corpus: incomplete root bundle header\n"); exit(1);
  }
  *strchr(line, '\n') = '\0';
  char *cursor = line;
  char *address = next_field(&cursor), *info = next_field(&cursor), *root = next_field(&cursor);
  char *magic = next_field(&cursor), *info_address = next_field(&cursor);
  if (!address || !info || !root || cursor || (magic == NULL) != (info_address == NULL)) {
    fprintf(stderr, "firmware corpus: malformed root bundle header\n"); exit(1);
  }
  struct root_bundle bundle = {parse_u64(address, "root address"),
    magic ? parse_u64(magic, "handoff magic") : UINT64_C(0x36d76289),
    info_address ? parse_u64(info_address, "handoff address") : UINT64_C(0x1000),
    read_byte_array(info), read_byte_array(root), lean_mk_empty_array(), lean_mk_empty_array()};
  size_t count = 0;
  while (fgets(line, sizeof(line), file)) {
    char *newline = strchr(line, '\n');
    if (!newline || ++count > 256) {
      fprintf(stderr, "firmware corpus: root bundle exceeds bounds\n"); exit(1);
    }
    *newline = '\0'; cursor = line;
    address = next_field(&cursor);
    char *table = next_field(&cursor);
    if (!address || !table || cursor) {
      fprintf(stderr, "firmware corpus: malformed physical table row\n"); exit(1);
    }
    bundle.addresses = lean_array_push(bundle.addresses, lean_box_uint64(parse_u64(address, "table address")));
    bundle.tables = lean_array_push(bundle.tables, read_byte_array(table));
  }
  if (ferror(file)) { fprintf(stderr, "firmware corpus: root bundle read failed\n"); exit(1); }
  fclose(file);
  return bundle;
}



static lean_object *run_host(int argc, char **argv) {
  (void)argc; (void)argv;
  leanos_register_boundary_target("leanos_qotom_bootstrap_query",
      (void *)(uintptr_t)&leanos_qotom_bootstrap_query);
  const char *path = getenv("LEANOS_QOTOM_BOOTSTRAP_REPLAY");
  if (!path) path = "build/qotom-bootstrap-corpus/replay.tsv";
  FILE *file = fopen(path, "r");
  if (!file) { perror(path); exit(1); }
  char line[MAX_LINE];
  unsigned inputs = 0;
  while (fgets(line, sizeof(line), file)) {
    if (line[0] == '#') continue;
    char *end = strchr(line, '\n');
    if (!end) { fputs("unterminated bootstrap row\n", stderr); exit(1); }
    *end = '\0';
    char *cursor = line, *fields[8];
    for (unsigned i = 0; i < 8; ++i) {
      fields[i] = next_field(&cursor);
      if (!fields[i]) { fputs("incomplete bootstrap row\n", stderr); exit(1); }
    }
    if (cursor) { fputs("extra bootstrap row fields\n", stderr); exit(1); }
    struct root_bundle bundle = read_root_bundle(fields[1]);
    uint64_t args[5], expected[6];
    for (unsigned i = 0; i < 5; ++i) args[i] = parse_u64(fields[i+2], "bootstrap scalar");
    char *token = strtok(fields[7], ",");
    for (unsigned i = 0; i < 6; ++i) {
      if (!token) { fputs("missing bootstrap word\n", stderr); exit(1); }
      expected[i] = parse_u64(token, "expected bootstrap word");
      token = strtok(NULL, ",");
    }
    if (token) { fputs("extra bootstrap word\n", stderr); exit(1); }
    for (unsigned word = 0; word < 6; ++word) {
      lean_inc(bundle.info); lean_inc(bundle.root);
      lean_inc(bundle.addresses); lean_inc(bundle.tables);
      uint64_t actual = leanos_qotom_bootstrap_query(bundle.magic, bundle.info_address,
          bundle.info, bundle.root, bundle.address, bundle.addresses, bundle.tables,
          args[0], args[1], args[2], args[3], args[4], word);
      printf("bootstrap %s word-%u %llu\n", fields[0], word, (unsigned long long)actual);
      if (actual != expected[word]) {
        fprintf(stderr, "bootstrap %s word %u: expected %llu, got %llu\n",
          fields[0], word, (unsigned long long)expected[word], (unsigned long long)actual);
        exit(1);
      }
    }
    lean_dec(bundle.info); lean_dec(bundle.root);
    lean_dec(bundle.addresses); lean_dec(bundle.tables);
    ++inputs;
  }
  fclose(file);
  if (!inputs) { fputs("empty bootstrap corpus\n", stderr); exit(1); }
  printf("Hosted generated-C bootstrap replay passed: %u inputs, %u words\n", inputs, inputs*6);
  return lean_io_result_mk_ok(lean_box(0));
}
int main(int argc, char **argv) {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  lean_object *result = initialize_leanos_LeanOS_QotomBootstrapABI(1);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(result)) {
    lean_dec(result);
    lean_init_task_manager();
    result = lean_run_main(&run_host, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_error(result)) {
    lean_io_result_show_error(result);
    lean_dec(result);
    return 1;
  }
  lean_dec(result);
  return 0;
}
