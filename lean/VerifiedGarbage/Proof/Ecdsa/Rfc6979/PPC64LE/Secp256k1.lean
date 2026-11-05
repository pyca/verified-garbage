module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: secp256k1

Its signature with a given `k` (`secp256k1Core`), as the proof's curve (`secp256k1R`), the
taint checks of the blocks that depend on it (`secp256k1_blk`), and the signature
with the HMAC of a table (`secp256k1T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_secp256k1_sign`, with secp256k1's group law `hL`. -/
def secp256k1Core (hL : Weierstrass.Law Spec.Secp256k1.curve) : Core where
  E := Spec.Ecdsa.Secp256k1.inst
  C := Impl.Ecdsa.PPC64LE.signSecp256k1
  N := "vg_ecdsa_secp256k1_sign"
  V := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.Secp256k1.sign_verified hL).2.1
  d := by decide +kernel

theorem secp256k1_nBits : Spec.Ecdsa.nBits Spec.Secp256k1.curve = 256 := by
  show Spec.Secp256k1.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.Secp256k1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.Secp256k1.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem secp256k1_sizes : (Spec.Secp256k1.curve.len = 24 ∨ Spec.Secp256k1.curve.len = 28 ∨ Spec.Secp256k1.curve.len = 32 ∨ Spec.Secp256k1.curve.len = 48 ∨ Spec.Secp256k1.curve.len = 64) ∧
    4 = (Spec.Secp256k1.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.Secp256k1.curve = 8 * Spec.Secp256k1.curve.len ∧ 2 ^ (8 * Spec.Secp256k1.curve.len) < 2 * Spec.Secp256k1.curve.n :=
  ⟨by decide, by decide, by rw [secp256k1_nBits]; decide, by decide +kernel⟩

theorem secp256k1_sh : 0 = 8 * Spec.Secp256k1.curve.len - Spec.Ecdsa.nBits Spec.Secp256k1.curve := by rw [secp256k1_nBits]; decide

theorem secp256k1_blk : RfcT (cfgC 4 32 false 0 Spec.Secp256k1.curve.n) := by rfcT_decide

/-- secp256k1, with the group law `hL`. -/
def secp256k1R (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcCurve where
  C := secp256k1Core hL
  w := 4
  big := false
  sizes := secp256k1_sizes
  sh := 0
  sh_eq := secp256k1_sh

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs) :
    Verified PPC64LE.target (signCodeT (secp256k1R hL) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ secp256k1_blk rfl hv (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
