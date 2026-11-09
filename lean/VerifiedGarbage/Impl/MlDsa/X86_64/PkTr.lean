module

public import VerifiedGarbage.Impl.MlKem.X86_64.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTr p (pk = rdi, tr = rsi, scratch = rdx)`: `tr = H(pk, 64)` (FIPS 204
Algorithm 8, line 6) of the parameter set `p`, as key generation computes it
(`KeyGen.trHash`): like ML-KEM's top-level functions
(`Impl/MlKem/X86_64/Frag.lean`), it saves its caller's callee-saved
registers in `scratch` at 840 and keeps `scratch` in `rbx`, `pk` in `r12`
and `tr` in `r13`; the Keccak state is at byte 0 of `scratch` and the sponge
functions' working space at 200. Every address and branch depends only on
the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.PkTr

open VG.X86_64
open VG.Impl.MlKem.X86_64 (hashAt topPro topEpi)
open VG.Spec.MlDsa (Params)

/-- Save the callee-saved registers; `rbx = scratch`, `r12 = pk`, `r13 = tr`. -/
def pro : List Instr := topPro .rdx [(.r12, .rdi), (.r13, .rsi)]

/-- `tr = H(pk, 64)`. -/
def hash (p : Params) : Prog isa := hashAt [((.r12, 0), p.pkLen)] 136 0x1f (.r13, 0) 64

/-- `vg_mldsa*_pk_tr` for the parameter set `p`. -/
def pkTr (p : Params) : Prog isa := .seq (.block pro) (.seq (hash p) (.block topEpi))

end VG.Impl.MlDsa.X86_64.PkTr
