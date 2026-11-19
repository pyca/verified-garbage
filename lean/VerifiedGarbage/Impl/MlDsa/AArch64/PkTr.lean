module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Frag
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Impl.Residue.AArch64.Union

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

/-! ## The function, as emitted

`vg_mldsa*_pk_tr` is its code above, then its cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared and the 16 bytes of stack it uses
are zeroed, so that it returns without secret residue. The registers are
those its own instructions write, stated here, and those the permutation it
calls states it writes (`Callee.clear`). -/

namespace VG.Impl.MlDsa.AArch64.Fn

open VG.Spec.MlDsa (Params)

/-- The registers `pk_tr` writes itself. -/
def pkTrOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v24, .v25, .v30,
   .v31],
   []⟩

/-- `vg_mldsa*_pk_tr` for the parameter set `p`, with the permutation `c`. -/
def pkTr (c : Impl.Sha3.AArch64.Callee) (p : Params) : Prog AArch64.isa :=
  Impl.Residue.AArch64.scrubAll 16 0 (pkTrOwn.union c.clear) (PkTr.pkTrWith c p)

end VG.Impl.MlDsa.AArch64.Fn
