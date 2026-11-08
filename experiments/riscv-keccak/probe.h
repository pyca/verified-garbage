#ifndef KECCAK_PROBE_H
#define KECCAK_PROBE_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef void (*perm_fn)(void *,void *);
#define CANDIDATES(X) X(f_leaf_row0) X(f_leaf_row2) X(asm_cache) X(sched2_1_16) X(sched2_2_16) X(sched3_2_16) X(sched2_2_32) X(sched3_2_32) X(sched2_2_268) X(sched3_2_268)
#define DECL(n) void candidate_##n(void*,void*);
CANDIDATES(DECL)
#undef DECL
#endif
