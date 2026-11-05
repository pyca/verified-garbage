module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.P521
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: P-521

Its signature with a given `k` (`p521Core`), as the proof's curve (`p521R`), the
taint checks of the blocks that depend on it (`p521_blk`), and the signature
with the HMAC of a table (`p521T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p521_sign`, with P-521's group law `hL`. -/
def p521Core (hL : Weierstrass.Law Spec.P521.curve) : Core where
  E := Spec.Ecdsa.P521.inst
  C := Impl.Ecdsa.PPC64LE.signP521
  N := "vg_ecdsa_p521_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P521.sign_verified hL).2.1
  d := by decide +kernel

theorem p521_nBits : Spec.Ecdsa.nBits Spec.P521.curve = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h₁ : 520 ≤ Spec.P521.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P521.curve.n.log2 < 521 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem p521_sizes : 9 = 9 ∧ Spec.P521.curve.len = 66 ∧ Spec.Ecdsa.nBits Spec.P521.curve = 521 :=
  ⟨rfl, by decide, p521_nBits⟩

theorem p521_sh : 7 = 8 * Spec.P521.curve.len - Spec.Ecdsa.nBits Spec.P521.curve := by rw [p521_nBits]; decide

theorem p521_blk : RfcT (cfgC 9 66 true 7 Spec.P521.curve.n) := by rfcT_decide

/-- P-521, with the group law `hL`. -/
def p521R (hL : Weierstrass.Law Spec.P521.curve) : RfcCurve where
  C := p521Core hL
  w := 9
  big := true
  sizes := p521_sizes
  sh := 7
  sh_eq := p521_sh

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs) :
    Verified PPC64LE.target (signCodeT (p521R hL) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ p521_blk rfl hv (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
