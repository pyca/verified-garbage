#ifndef KECCAK_PROBE_H
#define KECCAK_PROBE_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef void (*perm_fn)(void *,void *);
#define CANDIDATES(X) X(f_leaf_row0) X(f_leaf_row4parity) X(asm_row4) X(asm_row4parity)
#define DECL(n) void candidate_##n(void*,void*);
CANDIDATES(DECL)
#undef DECL
#endif
