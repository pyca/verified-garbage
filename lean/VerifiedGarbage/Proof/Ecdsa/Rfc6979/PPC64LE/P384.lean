module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Comb
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: P-384

Its signature with a given `k` (`p384Core`), as the proof's curve (`p384R`), the
taint checks of the blocks that depend on it (`p384_blk`), and the signature
with the HMAC of a table (`p384T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p384_sign`, with `[k]G` by the comb, and P-384's group law `hL`. -/
def p384Core (hL : Weierstrass.Law Spec.P384.curve) : Core where
  E := Spec.Ecdsa.P384.inst
  cs := Impl.Weierstrass.PPC64LE.p384CombConsts
  C := Impl.Ecdsa.PPC64LE.signP384Comb
  N := "vg_ecdsa_p384_sign_k"
  V := (Proof.Ecdsa.PPC64LE.P384.combSign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.P384.combSign_verified hL).2.1
  d := by lit_decide

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem p384_sizes : (Spec.P384.curve.len = 24 ∨ Spec.P384.curve.len = 28 ∨ Spec.P384.curve.len = 32 ∨ Spec.P384.curve.len = 48 ∨ Spec.P384.curve.len = 64) ∧
    6 = (Spec.P384.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.P384.curve = 8 * Spec.P384.curve.len ∧ 2 ^ (8 * Spec.P384.curve.len) < 2 * Spec.P384.curve.n :=
  ⟨by decide, by decide, by rw [p384_nBits]; decide, by decide +kernel⟩

theorem p384_sh : 0 = 8 * Spec.P384.curve.len - Spec.Ecdsa.nBits Spec.P384.curve := by rw [p384_nBits]; decide

theorem p384_blk : RfcT (cfgC 6 48 false 0 Spec.P384.curve.n) := by rfcT_decide

/-- P-384, with the group law `hL`. -/
def p384R (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  C := p384Core hL
  w := 6
  big := false
  sizes := p384_sizes
  sh := 0
  sh_eq := p384_sh

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs ∧ "VG_P384_COMB" ∉ Proof.HmacTable.PPC64LE.names vs) :
    Verified PPC64LE.target (signCodeT (p384R hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Weierstrass.PPC64LE.p384CombConsts vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ p384_blk rfl hv.1
    (sat_one hv.1 Proof.P384.PPC64LE.combSatMem hv.2
      (by rw [Proof.P384.PPC64LE.comb_words_length]; decide) Proof.P384.PPC64LE.combSatMem_held (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
