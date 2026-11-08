#ifndef KECCAK_PROBE_H
#define KECCAK_PROBE_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef void (*perm_fn)(void *,void *);
#define CANDIDATES(X) X(memory) X(row0) X(row1) X(row2) X(row3) X(cache2) X(cache4) X(cache5) X(scalar1) X(scalar2) X(scalar4)
#define DECL(n) void candidate_##n(void*,void*);
CANDIDATES(DECL)
#undef DECL
#endif
