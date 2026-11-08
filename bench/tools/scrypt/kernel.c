#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* These symbols contain only bytes and branches from the generated crates. */
void vg_scrypt_blockmix(void *, size_t, void *, size_t, void *);
void vg_scrypt_romix(void *, size_t, void *, size_t, void *, size_t);

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t checksum(const unsigned char *b, size_t n) {
    uint64_t sum = 0;
    for (size_t k = 0; k < n; k++) sum = sum * 131 + b[k];
    return sum;
}

int main(int argc, char **argv) {
    if (argc != 6) return 2;
    size_t n = strtoull(argv[1], NULL, 0);
    size_t r = strtoull(argv[2], NULL, 0);
    size_t iterations = strtoull(argv[3], NULL, 0);
    size_t samples = strtoull(argv[4], NULL, 0);
    int blockmix = atoi(argv[5]);
    if (n < 2 || (n & (n - 1)) || !r || !iterations || !samples ||
        r > SIZE_MAX / 128 || n > SIZE_MAX / (128 * r) ||
        r > SIZE_MAX / 128 - 2) return 2;
    size_t bytes = 128 * r;
    unsigned char *b = aligned_alloc(64, bytes);
    unsigned char *y = aligned_alloc(64, bytes);
    unsigned char *v = aligned_alloc(64, bytes * n);
    unsigned char *scratch = aligned_alloc(64, 128 * (r + 2));
    if (!b || !y || !v || !scratch) return 3;
    memset(v, 0, bytes * n);
    memset(y, 0, bytes);
    memset(scratch, 0, 128 * (r + 2));
    for (size_t sample = 0; sample < samples; sample++) {
        for (size_t k = 0; k < bytes; k++) b[k] = (unsigned char)(k * 37 + 11);
        double start = now();
        for (size_t i = 0; i < iterations; i++) {
            if (blockmix) {
                vg_scrypt_blockmix(b, r, y, r, scratch);
                unsigned char *tmp = b;
                b = y;
                y = tmp;
            } else {
                vg_scrypt_romix(b, r, v, n * r, scratch, r + 2);
            }
        }
        double elapsed = now() - start;
        printf("%s,%zu,%zu,%zu,%zu,%.9f,%016lx\n",
               blockmix ? "blockmix" : "romix", n, r, iterations, sample,
               elapsed, (unsigned long)checksum(b, bytes));
    }
    free(b);
    free(y);
    free(v);
    free(scratch);
}
