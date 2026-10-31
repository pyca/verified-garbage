#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
/* Experimental fifth argument supplies the immutable table; not the public ABI. */
extern void sha_scalar(uint32_t *, const void *, uint64_t, void *, const uint64_t *);
extern void sha_table_loop(uint32_t *, const void *, uint64_t, void *, const uint64_t *);
typedef void (*fn)(uint32_t *, const void *, uint64_t, void *, const uint64_t *);
static const fn fs[] = {sha_scalar, sha_table_loop};
#include "constants.h"
static uint64_t scratch[166];
static uint32_t h[8], initial[8];
static uint8_t data[16384];
static volatile uint32_t checksum;
static uint64_t now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (uint64_t)t.tv_sec * 1000000000ULL + (uint64_t)t.tv_nsec;
}
static double measure(unsigned v, unsigned n, unsigned reps) {
    uint64_t t = now();
    for (unsigned i = 0; i < reps; i++) {
        memcpy(h, iv, sizeof h);
        fs[v](h, data, n, scratch, kt);
    }
    uint64_t dt = now() - t;
    checksum ^= h[0];
    return (double)dt / reps;
}
int main(int argc, char **argv) {
    (void)argv;
    if (argc == 1) {
        uint64_t n;
        while (fread(&n, 8, 1, stdin) == 1) {
            if (n > 3 || fread(initial, sizeof initial, 1, stdin) != 1) return 2;
            if (n && fread(data, 64*n, 1, stdin) != 1) return 3;
            for (unsigned v = 0; v < 2; v++) {
                memcpy(h, initial, sizeof h);
                fs[v](h, data, n, scratch, kt);
                if (fwrite(h, sizeof h, 1, stdout) != 1) return 4;
            }
        }
        return 0;
    }
    for (unsigned i = 0; i < sizeof data; i++) data[i] = (uint8_t)(17*i + 49);
    const unsigned sizes[] = {1, 16, 256};
    for (unsigned k = 0; k < 3; k++) {
        unsigned n = sizes[k], reps = 16384 / n;
        uint32_t want[8];
        memcpy(want, iv, sizeof want);
        fs[0](want, data, n, scratch, kt);
        memcpy(h, iv, sizeof h);
        fs[1](h, data, n, scratch, kt);
        if (memcmp(h, want, sizeof h)) return 5;
        for (unsigned v = 0; v < 2; v++) {
            uint64_t end = now() + 50000000;
            do { measure(v, n, reps); } while (now() < end);
        }
        for (unsigned sample = 0; sample < 25; sample++)
            for (unsigned i = 0; i < 2; i++) {
                unsigned v = (sample + i) % 2;
                printf("%u,%u,%u,%.3f\n", n, sample, v, measure(v, n, reps));
            }
    }
    return checksum == 0x12345678U ? 6 : 0;
}
