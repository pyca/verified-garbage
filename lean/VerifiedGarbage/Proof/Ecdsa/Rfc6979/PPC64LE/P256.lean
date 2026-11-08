module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256CombLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
meta import VerifiedGarbage.Spec.Ecdsa.P256
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256Comb
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: P-256

Its signature with a given `k` (`p256Core`), as the proof's curve (`p256R`), the
taint checks of the blocks that depend on it (`p256_blk`), and the signature
with the HMAC of a table (`p256T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_p256_sign`, with `[k]G` by the comb, and P-256's group law `hL`. -/
def p256Core (hL : Weierstrass.Law Spec.P256.curve) : Core where
  E := Spec.Ecdsa.P256.inst
  cs := Impl.Weierstrass.PPC64LE.p256CombConsts
  C := Impl.Ecdsa.PPC64LE.signP256Comb
  N := "vg_ecdsa_p256_sign_k"
  V := (Proof.Ecdsa.PPC64LE.combSign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.combSign_verified hL).2.1
  d := by lit_decide

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem p256_sizes : (Spec.P256.curve.len = 24 ∨ Spec.P256.curve.len = 28 ∨ Spec.P256.curve.len = 32 ∨ Spec.P256.curve.len = 48 ∨ Spec.P256.curve.len = 64) ∧
    4 = (Spec.P256.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.P256.curve = 8 * Spec.P256.curve.len ∧ 2 ^ (8 * Spec.P256.curve.len) < 2 * Spec.P256.curve.n :=
  ⟨by decide, by decide, by rw [p256_nBits]; decide, by decide +kernel⟩

theorem p256_sh : 0 = 8 * Spec.P256.curve.len - Spec.Ecdsa.nBits Spec.P256.curve := by rw [p256_nBits]; decide

theorem p256_blk : RfcT (cfgC 4 32 false 0 Spec.P256.curve.n) := by rfcT_decide

/-- P-256, with the group law `hL`. -/
def p256R (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve where
  C := p256Core hL
  w := 4
  big := false
  sizes := p256_sizes
  sh := 0
  sh_eq := p256_sh

/-- `vg_ecdsa_p256_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem p256T_verified (hL : Weierstrass.Law Spec.P256.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs ∧ "VG_P256_COMB" ∉ Proof.HmacTable.PPC64LE.names vs) :
    Verified PPC64LE.target (signCodeT (p256R hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Weierstrass.PPC64LE.p256CombConsts vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ p256_blk rfl hv.1
    (sat_one hv.1 Proof.P256.PPC64LE.combSatMem hv.2
      (by rw [Proof.P256.PPC64LE.comb_words_length]; decide) Proof.P256.PPC64LE.combSatMem_held (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
