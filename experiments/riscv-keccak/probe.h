#ifndef KECCAK_PROBE_H
#define KECCAK_PROBE_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef void (*perm_fn)(void *,void *);
#define CANDIDATES(X) X(memory) X(row0) X(row1) X(row2) X(row3) X(cache2) X(cache4) X(cache5) X(v_memory) X(v_row0) X(v_row1) X(v_row2) X(v_row3) X(v_cache2) X(v_cache4) X(v_cache5) X(f_memory) X(f_row0) X(f_row1) X(f_row2) X(f_row3) X(f_cache2) X(f_cache4) X(f_cache5) X(f_parity) X(scalar1) X(scalar2) X(scalar4)
#define DECL(n) void candidate_##n(void*,void*);
CANDIDATES(DECL)
#undef DECL
#endif
