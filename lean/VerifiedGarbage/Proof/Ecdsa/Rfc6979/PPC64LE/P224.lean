module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.P224
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: P-224

Its signature with a given `k` (`p224Core`), as the proof's curve (`p224R`), the
taint checks of the blocks that depend on it (`p224_blk`), and the signature
with the HMAC of a table (`p224T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p224_sign`, with P-224's group law `hL`. -/
def p224Core (hL : Weierstrass.Law Spec.P224.curve) : Core where
  E := Spec.Ecdsa.P224.inst
  C := Impl.Ecdsa.PPC64LE.signP224
  N := "vg_ecdsa_p224_sign"
  V := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P224.sign_verified hL).2.1
  d := by decide +kernel

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem p224_sizes : (Spec.P224.curve.len = 24 ∨ Spec.P224.curve.len = 28 ∨ Spec.P224.curve.len = 32 ∨ Spec.P224.curve.len = 48 ∨ Spec.P224.curve.len = 64) ∧
    4 = (Spec.P224.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.P224.curve = 8 * Spec.P224.curve.len ∧ 2 ^ (8 * Spec.P224.curve.len) < 2 * Spec.P224.curve.n :=
  ⟨by decide, by decide, by rw [p224_nBits]; decide, by decide +kernel⟩

theorem p224_sh : 0 = 8 * Spec.P224.curve.len - Spec.Ecdsa.nBits Spec.P224.curve := by rw [p224_nBits]; decide

theorem p224_blk : RfcT (cfgC 4 28 false 0 Spec.P224.curve.n) := by rfcT_decide

/-- P-224, with the group law `hL`. -/
def p224R (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve where
  C := p224Core hL
  w := 4
  big := false
  sizes := p224_sizes
  sh := 0
  sh_eq := p224_sh

/-- `vg_ecdsa_p224_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs) :
    Verified PPC64LE.target (signCodeT (p224R hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ p224_blk rfl hv (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
