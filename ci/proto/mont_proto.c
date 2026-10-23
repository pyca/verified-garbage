/* Throwaway prototype (not part of the library): Montgomery multiplication
 * kernels for 32-bit Arm, timed against each other on CI's Arm runners.
 * Every kernel computes a b R^-1 mod m (R = 2^(32 n)), fully reduced, and is
 * checked against a plain reference before it is timed. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if defined(__ARM_NEON)
#include <arm_neon.h>
#endif

typedef uint32_t u32;
typedef uint64_t u64;
#define MAXN 64

#define UMAAL(lo, hi, x, y) do { u64 t_ = (u64)(x) * (y) + (lo) + (hi); (lo) = (u32)t_; (hi) = (u32)(t_ >> 32); } while (0)

/* t[0..n] (t[n] in 0..1), below 2m, reduced into o. Constant time. */
static void csub(u32 *o, const u32 *t, const u32 *m, int n) {
    u32 d[MAXN], borrow = 0;
    for (int j = 0; j < n; j++) {
        u64 s = (u64)t[j] - m[j] - borrow;
        d[j] = (u32)s; borrow = (u32)(s >> 63);
    }
    u32 keep = (u32)0 - (u32)((t[n] < borrow)); /* all ones: t < m */
    for (int j = 0; j < n; j++) o[j] = d[j] ^ ((d[j] ^ t[j]) & keep);
}

/* Reference: CIOS with plain 64-bit arithmetic. */
static void ref(u32 *o, const u32 *a, const u32 *b, const u32 *m, u32 minv, int n) {
    u32 t[MAXN + 2] = {0};
    for (int i = 0; i < n; i++) {
        u64 c = 0;
        for (int j = 0; j < n; j++) { c += (u64)a[i] * b[j] + t[j]; t[j] = (u32)c; c >>= 32; }
        c += t[n]; t[n] = (u32)c; t[n + 1] = (u32)(c >> 32);
        u32 q = t[0] * minv; c = ((u64)q * m[0] + t[0]) >> 32;
        for (int j = 1; j < n; j++) { c += (u64)q * m[j] + t[j]; t[j - 1] = (u32)c; c >>= 32; }
        c += t[n]; t[n - 1] = (u32)c; t[n] = t[n + 1] + (u32)(c >> 32);
    }
    csub(o, t, m, n);
}

/* The hand-scheduled kernels (mont_kernels.S). */
struct ctx { const u32 *b, *m; u32 minv, n; const u32 *bm, *a; };
void k_fios1(u32 *t, const struct ctx *c);
void k_fios1p(u32 *t, const struct ctx *c);
void k_fios2(u32 *t, const struct ctx *c);

/* 1. The verified generic FIOS loop, as emitted today. */
__attribute__((noinline)) static void fios1(u32 *o, const u32 *a, const u32 *b, const u32 *m, u32 minv, int n) {
    u32 t[MAXN + 2] = {0};
    struct ctx c = {b, m, minv, (u32)n, 0, a};
    k_fios1(t, &c);
    csub(o, t, m, n);
}

/* 2. FiosFast's pipelined scan in a loop over any width. */
__attribute__((noinline)) static void fios1p(u32 *o, const u32 *a, const u32 *b, const u32 *m, u32 minv, int n) {
    u32 t[MAXN + 2] = {0};
    struct ctx c = {b, m, minv, (u32)n, 0, a};
    k_fios1p(t, &c);
    csub(o, t, m, n);
}

/* 3. Two rows a pass, b and m interleaved first (counted in its time). */
__attribute__((noinline)) static void fios2(u32 *o, const u32 *a, const u32 *b, const u32 *m, u32 minv, int n) {
    u32 t[MAXN + 2] = {0}, bm[2 * MAXN];
    for (int j = 0; j < n; j++) { bm[2 * j] = b[j]; bm[2 * j + 1] = m[j]; }
    struct ctx c = {b, m, minv, (u32)n, bm, a};
    k_fios2(t, &c);
    csub(o, t, m, n);
}

#if defined(__ARM_NEON)
/* 4. Product scanning with NEON: column k sums a_i b_(k-i) and q_j m_(k-j)
 * four products an iteration (two vmull.u32, two accumulator pairs), into a sum of the 64-bit products
 * modulo 2^64 and an exact sum of their high words (as the x86 SSE2
 * kernel), against reversed copies of b and m; zero padding rounds every
 * column's range to whole pairs. */
__attribute__((noinline)) static void neon_ps(u32 *o, const u32 *a, const u32 *b, const u32 *m, u32 minv, int n) {
    /* xs: a or q at [PAD + i]; rv: b or m reversed, at [PAD + n - 1 - t]. */
    enum { PAD = 4 };
    u32 A[MAXN + 2 * PAD] = {0}, Q[MAXN + 2 * PAD] = {0};
    u32 BR[MAXN + 2 * PAD] = {0}, MR[MAXN + 2 * PAD] = {0}, t[MAXN + 1];
    for (int i = 0; i < n; i++) { A[PAD + i] = a[i]; BR[PAD + n - 1 - i] = b[i]; MR[PAD + n - 1 - i] = m[i]; }
    u64 c = 0; /* the carry into the column */
    for (int k = 0; k < 2 * n; k++) {
        uint64x2_t full = vdupq_n_u64(0), high = vdupq_n_u64(0);
        int lo = k - n + 1 < 0 ? 0 : k - n + 1, hi = k < n - 1 ? k : n - 1;
        /* a_i b_(k-i), i in lo..hi: b_(k-i) = BR[PAD + n - 1 - k + i]. */
        uint64x2_t full2 = vdupq_n_u64(0), high2 = vdupq_n_u64(0);
        for (int i = lo & ~3; i <= hi; i += 4) {
            uint32x4_t x = vld1q_u32(&A[PAD + i]), y = vld1q_u32(&BR[PAD + n - 1 - k + i]);
            uint64x2_t p = vmull_u32(vget_low_u32(x), vget_low_u32(y));
            uint64x2_t p2 = vmull_u32(vget_high_u32(x), vget_high_u32(y));
            full = vaddq_u64(full, p); high = vsraq_n_u64(high, p, 32);
            full2 = vaddq_u64(full2, p2); high2 = vsraq_n_u64(high2, p2, 32);
        }
        /* q_j m_(k-j), j in lo..min(hi, k - 1) (q_k comes next). */
        int hj = hi < k - 1 ? hi : k - 1;
        for (int j = lo & ~3; j <= hj; j += 4) {
            uint32x4_t x = vld1q_u32(&Q[PAD + j]), y = vld1q_u32(&MR[PAD + n - 1 - k + j]);
            uint64x2_t p = vmull_u32(vget_low_u32(x), vget_low_u32(y));
            uint64x2_t p2 = vmull_u32(vget_high_u32(x), vget_high_u32(y));
            full = vaddq_u64(full, p); high = vsraq_n_u64(high, p, 32);
            full2 = vaddq_u64(full2, p2); high2 = vsraq_n_u64(high2, p2, 32);
        }
        full = vaddq_u64(full, full2); high = vaddq_u64(high, high2);
        /* Pairs that overrun the range read the zero padding of A, Q, BR
         * or MR (Q[PAD + k] is written only after this column). */
        u64 h = vgetq_lane_u64(high, 0) + vgetq_lane_u64(high, 1);
        u64 l = (vgetq_lane_u64(full, 0) - (vgetq_lane_u64(high, 0) << 32))
              + (vgetq_lane_u64(full, 1) - (vgetq_lane_u64(high, 1) << 32));
        /* column = 2^32 h + l + c; its word w, then c = (column - w) / 2^32 */
        u64 s = (u64)(u32)l + (u32)c;
        u32 w = (u32)s;
        c = h + (l >> 32) + (c >> 32) + (s >> 32);
        if (k < n) {
            u32 q = w * minv;
            Q[PAD + k] = q;
            c += ((u64)q * MR[PAD + n - 1] + w) >> 32; /* q m_0 cancels w */
        } else {
            t[k - n] = w;
        }
    }
    t[n] = (u32)c;
    csub(o, t, m, n);
}
#endif

/* Montgomery constant: -m^-1 mod 2^32. */
static u32 neg_inv(u32 m0) { u32 x = 1; for (int i = 0; i < 5; i++) x *= 2 - m0 * x; return (u32)0 - x; }

static u64 rng = 0x9e3779b97f4a7c15ull;
static u32 rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (u32)rng; }

/* a random number below m */
static void below(u32 *x, const u32 *m, int n) {
    for (int j = 0; j < n; j++) x[j] = rnd();
    x[n - 1] %= m[n - 1];
}

typedef void (*kernel)(u32 *, const u32 *, const u32 *, const u32 *, u32, int);
struct impl { const char *name; kernel f; int even; };

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

int main(int argc, char **argv) {
    struct impl impls[] = {
        {"fios1", fios1, 0}, {"fios1p", fios1p, 0}, {"fios2", fios2, 1},
#if defined(__ARM_NEON)
        {"neon_ps", neon_ps, 0},
#endif
    };
    int nimpl = sizeof impls / sizeof impls[0];
    int sizes[] = {16, 32, 48, 64};
    double budget = argc > 1 ? atof(argv[1]) : 0.3;
    int fail = 0;
    /* Correctness, including the largest operands. */
    for (int si = 0; si < 4; si++) {
        int n = sizes[si];
        for (int trial = 0; trial < 300; trial++) {
            u32 m[MAXN], a[MAXN], b[MAXN], r[MAXN], o[MAXN];
            for (int j = 0; j < n; j++) m[j] = rnd();
            m[0] |= 1; if (trial % 3 == 0) m[n - 1] |= 0x80000000u; if (trial % 5 == 0) for (int j = 0; j < n; j++) m[j] = 0xffffffffu;
            below(a, m, n); below(b, m, n);
            if (trial % 7 == 0) { memcpy(a, m, 4 * n); a[0] -= 1; memcpy(b, a, 4 * n); }
            u32 minv = neg_inv(m[0]);
            ref(r, a, b, m, minv, n);
            for (int k = 0; k < nimpl; k++) {
                impls[k].f(o, a, b, m, minv, n);
                if (memcmp(o, r, 4 * n)) { printf("MISMATCH %s n=%d trial=%d\n", impls[k].name, n, trial); fail = 1; }
            }
        }
    }
    if (fail) return 1;
    printf("all kernels agree with the reference\n");
    printf("%-8s", "n");
    for (int k = 0; k < nimpl; k++) printf(" %12s", impls[k].name);
    printf("   (ns per multiplication, best of 7; speedup vs fios1)\n");
    for (int si = 0; si < 4; si++) {
        int n = sizes[si];
        u32 m[MAXN], a[MAXN], b[MAXN];
        for (int j = 0; j < n; j++) m[j] = rnd();
        m[0] |= 1; m[n - 1] |= 0x80000000u;
        below(a, m, n); below(b, m, n);
        u32 minv = neg_inv(m[0]);
        double best[8];
        for (int k = 0; k < nimpl; k++) {
            /* calibrate */
            long iters = 1; double el;
            for (;;) { double t0 = now(); for (long it = 0; it < iters; it++) impls[k].f(a, a, b, m, minv, n); el = now() - t0; if (el > budget / 10) break; iters *= 2; }
            iters = (long)(iters * (budget / 7) / el) + 1;
            best[k] = 1e30;
            for (int rep = 0; rep < 7; rep++) {
                double t0 = now();
                for (long it = 0; it < iters; it++) impls[k].f(a, a, b, m, minv, n);
                double ns = (now() - t0) * 1e9 / iters;
                if (ns < best[k]) best[k] = ns;
            }
        }
        printf("%-8d", n);
        for (int k = 0; k < nimpl; k++) printf(" %7.0f %4.2fx", best[k], best[0] / best[k]);
        printf("\n");
    }
    return 0;
}
