/* Differential-fuzz runner: executes device-program images with the
   deterministic device model of tests/WifiFuzz.lean and prints one summary
   line per image, which must equal the simulator's line for the same image.
   usage: fuzz-runner image.bin... */
#include <stdio.h>
#include <stdlib.h>
#include "wifi-exec.h"
#include "fuzz-model.h"

int main(int argc, char **argv) {
    static uint8_t image[1 << 20];
    static char line[512];
    for (int k = 1; k < argc; ++k) {
        FILE *f = fopen(argv[k], "rb");
        if (!f) { perror(argv[k]); return 2; }
        size_t len = fread(image, 1, sizeof image, f);
        fclose(f);
        fuzz_summary(image, (uint32_t)len, wifi_resume, line, sizeof line);
        printf("%s\n", line);
    }
    return 0;
}
