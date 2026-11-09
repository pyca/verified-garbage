module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on AArch64: `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTrWith c p (pk = x0, tr = x1, scratch = x2)`: `tr = H(pk, 64)` (FIPS 204
Algorithm 8, line 6) of the parameter set `p`, as key generation computes it,
with the Keccak backend `c`. It copies `scratch` to `x3`, so that key
generation's prologue (`KeyGen.pro`) saves the caller's registers in
`scratch` and keeps `pk` in `x25`, `tr` in `x26` and `scratch` in `x28`;
then SHAKE256 of the `pkLen` bytes at `pk` to the 64 bytes at `tr`, with the
Keccak state at `scratch + 0` and its working space at `scratch + 200`
(`KeyGen.shake256With`); then key generation's epilogue (`KeyGen.epi`),
which restores them. Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PkTr

open VG.AArch64
open VG.Impl.MlDsa.AArch64.KeyGen (pro epi shake256With)
open VG.Spec.MlDsa (Params)

/-- `x3 ← scratch`. -/
def enter : List Instr := [.addImm .x .x3 .x2 0]

/-- `vg_mldsa*_pk_tr` for the parameter set `p`, with the Keccak backend `c`. -/
def pkTrWith (c : Impl.Sha3.AArch64.Callee) (p : Params) : Prog isa :=
  .seq (.block enter) (.seq (.block pro) (.seq (shake256With c [⟨.x25, 0, p.pkLen⟩] [⟨.x26, 0, 64⟩]) (.block epi)))

end VG.Impl.MlDsa.AArch64.PkTr
