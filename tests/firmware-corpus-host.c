/* Hosted generated-C replay of the firmware handoff corpus.
 *
 * scripts/firmware-corpus.py normalizes every captured real-firmware memory
 * map and MADT (and each derived mutation) into the exact decoder inputs and
 * writes build/firmware-corpus/replay.tsv: one row per input naming the
 * stage, the normalized file, the two scalar boundary arguments, and every
 * expected result word. This harness feeds each file through the same
 * exported boundaries the boot path uses and holds the generated C to the
 * manifest words that the Lean checks (Corpus.lean) also prove. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define LEANOS_BOUNDARY_ABI_OBJECTS 1
#include "boundary-abi.h"

extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_BootMemoryMapDecoderABI(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);
#define REGISTER_BOUNDARY(symbol)                                               \
  leanos_register_boundary_target(#symbol, (void *)(uintptr_t)&symbol)

#define MAX_LINE 16384
#define MAX_WORDS 4096

static const char *replay_path(void) {
  const char *path = getenv("LEANOS_FIRMWARE_CORPUS_REPLAY");
  return path != NULL && path[0] != '\0' ? path
                                         : "build/firmware-corpus/replay.tsv";
}

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

static lean_object *run_host(int argc, char **argv) {
  (void)argc;
  (void)argv;
  REGISTER_BOUNDARY(leanos_boot_handoff_query);
  REGISTER_BOUNDARY(leanos_boot_complete_topology_query);

  const char *path = replay_path();
  FILE *replay = fopen(path, "r");
  if (replay == NULL) {
    fprintf(stderr, "firmware corpus: cannot open replay driver %s\n", path);
    exit(1);
  }
  static char line[MAX_LINE];
  static uint64_t expected[MAX_WORDS];
  unsigned long inputs = 0;
  unsigned long words = 0;
  while (fgets(line, sizeof(line), replay) != NULL) {
    if (line[0] == '#' || line[0] == '\n') {
      continue;
    }
    size_t length = strlen(line);
    if (length == 0 || line[length - 1] != '\n') {
      fprintf(stderr, "firmware corpus: replay row too long or unterminated\n");
      exit(1);
    }
    line[length - 1] = '\0';
    char *cursor = line;
    const char *input = next_field(&cursor);
    const char *stage = next_field(&cursor);
    const char *file = next_field(&cursor);
    const char *arg0 = next_field(&cursor);
    const char *arg1 = next_field(&cursor);
    char *word_list = next_field(&cursor);
    if (input == NULL || stage == NULL || file == NULL || arg0 == NULL ||
        arg1 == NULL || word_list == NULL || cursor != NULL) {
      fprintf(stderr, "firmware corpus: replay row has the wrong field count\n");
      exit(1);
    }
    size_t count = 0;
    for (char *token = strtok(word_list, ","); token != NULL;
         token = strtok(NULL, ",")) {
      if (count == MAX_WORDS) {
        fprintf(stderr, "firmware corpus: %s pins too many words\n", input);
        exit(1);
      }
      expected[count++] = parse_u64(token, "expected word");
    }
    if (count < 3) {
      fprintf(stderr, "firmware corpus: %s pins fewer than three words\n", input);
      exit(1);
    }
    uint64_t first = parse_u64(arg0, "argument");
    uint64_t second = parse_u64(arg1, "argument");
    int handoff = strcmp(stage, "handoff") == 0;
    if (!handoff && strcmp(stage, "madt") != 0) {
      fprintf(stderr, "firmware corpus: %s has unknown stage %s\n", input, stage);
      exit(1);
    }
    lean_object *bytes = read_byte_array(file);
    for (size_t word = 0; word < count; ++word) {
      /* Both exports consume their byte-array argument; keep this loop's
       * reference alive across the words and release it once at the end. */
      lean_inc(bytes);
      uint64_t actual =
          handoff ? leanos_boot_handoff_query(first, second, bytes, word)
                  : leanos_boot_complete_topology_query(bytes, first, second,
                                                        word);
      printf("firmware-corpus %s %s word-%zu %llu\n", input, stage, word,
             (unsigned long long)actual);
      if (actual != expected[word]) {
        fprintf(stderr,
                "firmware corpus: %s %s word %zu: expected %llu, got %llu\n",
                input, stage, word, (unsigned long long)expected[word],
                (unsigned long long)actual);
        exit(1);
      }
    }
    lean_dec(bytes);
    inputs += 1;
    words += count;
  }
  fclose(replay);
  if (inputs == 0) {
    fprintf(stderr, "firmware corpus: replay driver %s lists no inputs\n", path);
    exit(1);
  }
  printf("Hosted generated-C firmware corpus replay passed: %lu inputs, %lu words\n",
         inputs, words);
  return lean_io_result_mk_ok(lean_box(0));
}

int main(int argc, char **argv) {
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  lean_object *result = initialize_leanos_LeanOS_BootMemoryMapDecoderABI(1);
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
