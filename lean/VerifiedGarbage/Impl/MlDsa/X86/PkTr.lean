module

public import VerifiedGarbage.Impl.MlKem.X86.Top
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa44_pk_tr`, `vg_mldsa65_pk_tr`, `vg_mldsa87_pk_tr`

`pkTr p (pk, tr, scratch)`: `tr = H(pk, 64)` (FIPS 204 Algorithm 8, line 6)
of the parameter set `p`, as key generation computes it (`KeyGen.trHash`):
a leaf (`Impl.MlKem.X86.leaf`) that keeps `scratch` (argument 2) in `esi`,
with the Keccak state at its byte 0 and the sponge functions' working space
at 200, and calls of the sponge functions. Every address and branch depends
only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.PkTr

open VG.X86
open VG.Impl.MlKem.X86 (hash1 leaf at_)
open VG.Spec.MlDsa (Params)

/-- `scratch` is argument 2. -/
abbrev kS : Nat := 2

/-- The body: `esi ← scratch`, then `tr = H(pk, 64)`. -/
def body (p : Params) : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * kS)))]) (hash1 kS 0 200 136 0x1f ⟨0, 0, p.pkLen⟩ ⟨1, 0, 64⟩)

/-- `vg_mldsa*_pk_tr` for the parameter set `p`. -/
def pkTr (p : Params) : Prog isa := leaf (body p)

end VG.Impl.MlDsa.X86.PkTr
