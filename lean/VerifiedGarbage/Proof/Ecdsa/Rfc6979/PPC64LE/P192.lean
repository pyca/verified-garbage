module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: P-192

Its signature with a given `k` (`p192Core`), as the proof's curve (`p192R`), the
taint checks of the blocks that depend on it (`p192_blk`), and the signature
with the HMAC of a table (`p192T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p192_sign`, with P-192's group law `hL`. -/
def p192Core (hL : Weierstrass.Law Spec.P192.curve) : Core where
  E := Spec.Ecdsa.P192.inst
  C := Impl.Ecdsa.PPC64LE.signP192
  N := "vg_ecdsa_p192_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P192.sign_verified hL).2.1
  d := by decide +kernel

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem p192_sizes : (Spec.P192.curve.len = 24 ∨ Spec.P192.curve.len = 28 ∨ Spec.P192.curve.len = 32 ∨ Spec.P192.curve.len = 48 ∨ Spec.P192.curve.len = 64) ∧
    3 = (Spec.P192.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.P192.curve = 8 * Spec.P192.curve.len ∧ 2 ^ (8 * Spec.P192.curve.len) < 2 * Spec.P192.curve.n :=
  ⟨by decide, by decide, by rw [p192_nBits]; decide, by decide +kernel⟩

theorem p192_sh : 0 = 8 * Spec.P192.curve.len - Spec.Ecdsa.nBits Spec.P192.curve := by rw [p192_nBits]; decide

theorem p192_blk : RfcT (cfgC 3 24 false 0 Spec.P192.curve.n) := by rfcT_decide

/-- P-192, with the group law `hL`. -/
def p192R (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve where
  C := p192Core hL
  w := 3
  big := false
  sizes := p192_sizes
  sh := 0
  sh_eq := p192_sh

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs) :
    Verified PPC64LE.target (signCodeT (p192R hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ p192_blk rfl hv (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
