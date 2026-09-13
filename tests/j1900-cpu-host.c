#include <lean/lean.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <stdio.h>
#include "boundary-abi.h"
#include "../build/j1900/raw-cases.h"
#include "../build/j1900/msr-cases.h"

extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_J1900CpuProfile(uint8_t);
extern lean_object *initialize_leanos_LeanOS_J1900MsrReadback(uint8_t);
extern lean_object *initialize_leanos_LeanOS_J1900CpuControlPolicy(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);

static uint64_t cpu_control_policy(const uint64_t *c, const uint64_t *m,
                                   uint64_t word) {
  return leanos_j1900_cpu_control_policy_query(
      c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8], c[9],
      c[10], c[11], c[12], c[13], c[14], c[15], c[16], c[17], c[18],
      c[19], c[20], c[21], m[0], m[1], m[2], m[3], m[4], m[5], m[6],
      m[7], word);
}

static int decimal_word(const char *text, uint64_t *word) {
  if (!*text || (text[0] == '0' && text[1])) return 0;
  uint64_t value = 0;
  for (; *text; ++text) {
    if (*text < '0' || *text > '9') return 0;
    unsigned digit = (unsigned)(*text - '0');
    if (value > (UINT64_MAX - digit) / 10) return 0;
    value = value * 10 + digit;
  }
  *word = value;
  return 1;
}

int main(int argc, char **argv) {
  lean_initialize();
  lean_object *init = initialize_leanos_LeanOS_J1900CpuProfile(1);
  if (lean_io_result_is_error(init)) {
    lean_io_result_show_error(init);
    lean_dec_ref(init);
    return 2;
  }
  lean_dec_ref(init);
  init = initialize_leanos_LeanOS_J1900MsrReadback(1);
  if (lean_io_result_is_error(init)) {
    lean_io_result_show_error(init);
    lean_dec_ref(init);
    return 2;
  }
  lean_dec_ref(init);
  init = initialize_leanos_LeanOS_J1900CpuControlPolicy(1);
  if (lean_io_result_is_error(init)) {
    lean_io_result_show_error(init);
    lean_dec_ref(init);
    return 2;
  }
  lean_dec_ref(init);
  lean_io_mark_end_initialization();
  leanos_register_boundary_target("leanos_j1900_msr_readback",
      (void *)(uintptr_t)&leanos_j1900_msr_readback);
  for (size_t i = 0; i < sizeof(msr_cases) / sizeof(msr_cases[0]); ++i) {
    const uint64_t *w = msr_cases[i];
    if (leanos_j1900_msr_readback(w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]) != w[8]) {
      fprintf(stderr, "J1900 MSR boundary case %zu failed\n", i);
      return 1;
    }
  }
  leanos_register_boundary_target("leanos_j1900_cpu_select",
      (void *)(uintptr_t)&leanos_j1900_cpu_select);
  for (size_t i = 0; i < sizeof(cpu_cases) / sizeof(cpu_cases[0]); ++i) {
    const uint64_t *w = cpu_cases[i];
    uint64_t actual = leanos_j1900_cpu_select(
        w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9],
        w[10], w[11], w[12], w[13], w[14], w[15], w[16], w[17], w[18],
        w[19], w[20], w[21]);
    if (actual != w[22]) {
      fprintf(stderr, "J1900 CPU boundary case %zu failed\n", i);
      return 1;
    }
  }
  leanos_register_boundary_target("leanos_j1900_cpu_control_policy_query",
      (void *)(uintptr_t)&leanos_j1900_cpu_control_policy_query);
  const uint64_t *denied_msrs = msr_cases[0];
  for (size_t i = 0; i < sizeof(cpu_cases) / sizeof(cpu_cases[0]); ++i) {
    const uint64_t *c = cpu_cases[i];
    int accepted = c[22] == UINT64_C(0x10000);
    const uint64_t expected[8] = {
      1, accepted ? 1 : 2, accepted ? 0 : c[22], accepted ? 1 : 0,
      accepted ? UINT64_C(0x10000) : 0, accepted ? 1 : 0,
      accepted ? 1 : 0, 0
    };
    for (uint64_t word = 0; word < 8; ++word) {
      if (cpu_control_policy(c, denied_msrs, word) != expected[word]) {
        fprintf(stderr, "J1900 CPU/control CPU case %zu word %" PRIu64 " failed\n",
                i, word);
        return 1;
      }
    }
    if (cpu_control_policy(c, denied_msrs, 8) != 0) return 1;
  }
  const uint64_t *accepted_cpu = cpu_cases[0];
  for (size_t i = 0; i < sizeof(msr_cases) / sizeof(msr_cases[0]); ++i) {
    const uint64_t *m = msr_cases[i];
    int accepted = m[8] == 1;
    const uint64_t expected[8] = {
      1, accepted ? 1 : 2, accepted ? 0 : 13, accepted ? 1 : 0,
      accepted ? UINT64_C(0x10000) : 0, accepted ? 1 : 0,
      accepted ? 1 : 0, 0
    };
    for (uint64_t word = 0; word < 8; ++word) {
      if (cpu_control_policy(accepted_cpu, m, word) != expected[word]) {
        fprintf(stderr, "J1900 CPU/control MSR case %zu word %" PRIu64 " failed\n",
                i, word);
        return 1;
      }
    }
  }
  /* The capture checker supplies complete bounded observations to these same
     generated exports. Run the fixed corpus first in both CLI and test modes. */
  if (argc > 1) {
    int cpu = strcmp(argv[1], "cpu") == 0;
    int msr = strcmp(argv[1], "msr") == 0;
    int count = cpu ? 22 : 8;
    uint64_t w[22];
    if ((!cpu && !msr) || argc != count + 2) return 2;
    for (int i = 0; i < count; ++i)
      if (!decimal_word(argv[i + 2], &w[i])) return 2;
    uint64_t actual = cpu ? leanos_j1900_cpu_select(
        w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9],
        w[10], w[11], w[12], w[13], w[14], w[15], w[16], w[17], w[18],
        w[19], w[20], w[21]) : leanos_j1900_msr_readback(
        w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]);
    printf("%" PRIu64 "\n", actual);
    return 0;
  }
  puts("Hosted generated-C J1900 CPU replay passed");
  return 0;
}
