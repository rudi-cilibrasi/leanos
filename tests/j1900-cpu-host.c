#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include "boundary-abi.h"
#include "../build/j1900/raw-cases.h"
#include "../build/j1900/msr-cases.h"

extern void lean_initialize(void);
extern lean_object *initialize_leanos_LeanOS_J1900CpuProfile(uint8_t);
extern lean_object *initialize_leanos_LeanOS_J1900MsrReadback(uint8_t);
extern void leanos_register_boundary_target(const char *, void *);

int main(void) {
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
  puts("Hosted generated-C J1900 CPU replay passed");
  return 0;
}
