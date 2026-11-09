/* The state of the law image_exact (harness/image_exact.c): the call main makes and the law's own reading of the
   image.  env/image_exact.c reads it too, to shape native and interpreter runs; it is part of no theorem through
   the env. */
#ifndef LEANOS_IMAGE_EXACT_H
#define LEANOS_IMAGE_EXACT_H
#include <stdint.h>
#include "device_program_api.h"

/* The function main calls. */
#define CALL_HEADER 0u   /* wifi_image_header */
#define CALL_START 1u    /* wifi_start */
#define CALL_WITHIN 2u   /* wifi_policy_within */
#define CALL_SERVICE 3u  /* wifi_service_admitted */
#define CALL_SOURCE 4u   /* wifi_source_admitted */

/* The law's reading of an image: the status wifi_image_header must return and, when it is 0, the target, policy
   and header length it must write; for wifi_start, whether the instruction count and blob length fit. */
struct law_image {
    uint32_t status, header_len;
    struct wifi_target t;
    struct wifi_policy pol;
    uint32_t n, blob_len, start_status;
};

struct law {
    uint32_t call, length;
    uint8_t *copy;           /* the law's own copy of the image's bytes */
    struct law_image want;
};
extern struct law law;
#endif
