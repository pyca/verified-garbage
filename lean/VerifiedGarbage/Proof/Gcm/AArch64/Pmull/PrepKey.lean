module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# GHASH with PMULL: the prepared powers are its keys

The prepared encoding of `Hᵏ` (`pp H k`, `Spec.Gcm.preparedPower`) is the
key `vg_ghash_aes` multiplies by `Hᵏ` with: `H'` is `pp H 1` and `mul`
multiplies prepared powers (`PrepPow`, the algebra of `Arith.lean`, proven
in `Pmull/Prepared.lean`), so that the proofs of the code that computes and
reads them take it as a hypothesis, as `MulKey`, without importing the
algebra.
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (poly)

/-- The prepared encoding of `Hᵏ`. -/
def pp (H : Spec.Gcm.Block) (k : Nat) : BitVec 128 := Spec.Gcm.preparedPower (Spec.Gcm.hpow H k)

/-- `H'` is the prepared power of `H`, and `mul` of prepared powers (the
first as loaded) is the prepared power of the product. -/
structure PrepPow : Prop where
  key : ∀ H, keyV H = pp H 1
  mul : ∀ H a b, mulV (ext8 (pp H a) (pp H a)) (pp H b) = ext8 (pp H (a + b)) (pp H (a + b))

end VG.Proof.Gcm.AArch64.Pmull
