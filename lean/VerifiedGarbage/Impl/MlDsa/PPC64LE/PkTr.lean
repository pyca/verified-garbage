module

public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on PPC64LE: `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTr p (pk = r3, tr = r4, scratch = r5)`: `tr = H(pk, 64)` (FIPS 204
Algorithm 8, line 6) of the parameter set `p`, as key generation computes it
(`KeyGen.trHash`): like the other top-level functions
(`Impl/MlDsa/PPC64LE/KeyGen/Frag.lean`), it saves our caller's `r24`–`r31`
and our return address in `scratch` at 840 (from `r6`, a copy of `scratch`),
and keeps `scratch` in `r31`, `pk` in `r29` (and `r30`, the third pointer of
that layout) and `tr` in `r28`; the Keccak state is at byte 0 of `scratch`
and the sponge functions' working space at 200. Every address and branch
depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.PkTr

open VG.PPC64LE
open VG.Impl.MlKem.PPC64LE (hash topSave topEnd)
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Spec.MlDsa (Params)

/-- `r6 ← scratch`; save our caller's registers; `r31 = scratch`, `r30 = r29 = pk`, `r28 = tr`. -/
def pro : List Instr :=
  [mov .r6 .r5] ++ topSave .r6 ++ ([mov .r30 .r3, mov .r29 .r3, mov .r28 .r4, mov .r31 .r6, .li .r24 1] : List Instr)

/-- `tr = H(pk, 64)`. -/
def trHash (p : Params) : Prog isa := hash 136 0x1f [⟨.r29, 0, p.pkLen⟩] [⟨.r28, 0, 64⟩]

/-- `vg_mldsa*_pk_tr` for the parameter set `p`. -/
def pkTr (p : Params) : Prog isa := .seq (.block pro) (.seq (trHash p) (.block topEnd))

end VG.Impl.MlDsa.PPC64LE.PkTr
