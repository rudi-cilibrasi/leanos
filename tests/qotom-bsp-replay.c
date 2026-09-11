#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/qotom_bsp_consumer.h"
static int scalar(const char *s, uint64_t *value) {
    if (!*s || (*s == '0' && s[1])) return 0;
    for (const char *p = s; *p; ++p) if (*p < '0' || *p > '9') return 0;
    char *end;
    errno = 0;
    unsigned long long parsed = strtoull(s,&end,10);
    if (errno || *end || parsed > UINT64_MAX) return 0;
    *value = (uint64_t)parsed;
    return 1;
}
int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1],"--identity")) {
        puts("LeanOS native BSP replay v1"); return 0;
    }
    if (argc != 7) return 2;
    struct qotom_bsp_observation obs;
    if (!scalar(argv[2],&obs.executing) || !scalar(argv[3],&obs.cpuid_edx) ||
        !scalar(argv[4],&obs.available) || !scalar(argv[5],&obs.apic_base) ||
        !scalar(argv[6],&obs.sample_id)) return 2;
    uint8_t bytes[65537];
    FILE *file = fopen(argv[1],"rb");
    if (!file) return 3;
    size_t length = fread(bytes,1,sizeof(bytes),file);
    int failed = ferror(file);
    if (fclose(file)) failed = 1;
    if (failed || length <= 44 || length > 65536 || memcmp(bytes,"APIC",4)) return 3;
    uint32_t declared = (uint32_t)bytes[4] | (uint32_t)bytes[5] << 8 |
        (uint32_t)bytes[6] << 16 | (uint32_t)bytes[7] << 24;
    uint8_t checksum = 0;
    for (size_t i = 0; i < length; ++i) checksum = (uint8_t)(checksum + bytes[i]);
    if (declared != length || checksum) return 3;
    struct qotom_bsp_result r = qotom_bind_validated_madt_entries(bytes+44,length-44,&obs);
    printf("%"PRIu64" %"PRIu64" %"PRIu64" %"PRIu64" %"PRIu64" %"PRIu64"\n",
        r.status,r.detail,r.offset,r.apic_id,r.processor_count,r.apic_base);
    return 0;
}
