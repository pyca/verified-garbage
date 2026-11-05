module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: brainpoolP384r1

Its signature with a given `k` (`brainpoolp384r1Core`), as the proof's curve (`brainpoolp384r1R`), the
taint checks of the blocks that depend on it (`brainpoolp384r1_blk`), and the signature
with the HMAC of a table (`brainpoolp384r1T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp384r1_sign`, with brainpoolP384r1's group law `hL`. -/
def brainpoolp384r1Core (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP384r1.inst
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP384r1
  N := "vg_ecdsa_brainpoolp384r1_sign"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP384r1.sign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP384r1.sign_verified hL).2.1
  d := by decide +kernel

theorem brainpoolp384r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 384 := by
  show Spec.BrainpoolP384r1.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.BrainpoolP384r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP384r1.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem brainpoolp384r1_sizes : (Spec.BrainpoolP384r1.curve.len = 24 ∨ Spec.BrainpoolP384r1.curve.len = 28 ∨ Spec.BrainpoolP384r1.curve.len = 32 ∨ Spec.BrainpoolP384r1.curve.len = 48 ∨ Spec.BrainpoolP384r1.curve.len = 64) ∧
    6 = (Spec.BrainpoolP384r1.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve = 8 * Spec.BrainpoolP384r1.curve.len ∧ 2 ^ (8 * Spec.BrainpoolP384r1.curve.len) < 2 * Spec.BrainpoolP384r1.curve.n :=
  ⟨by decide, by decide, by rw [brainpoolp384r1_nBits]; decide, by decide +kernel⟩

theorem brainpoolp384r1_sh : 0 = 8 * Spec.BrainpoolP384r1.curve.len - Spec.Ecdsa.nBits Spec.BrainpoolP384r1.curve := by rw [brainpoolp384r1_nBits]; decide

theorem brainpoolp384r1_blk : RfcT (cfgC 6 48 false 0 Spec.BrainpoolP384r1.curve.n) := by rfcT_decide

/-- brainpoolP384r1, with the group law `hL`. -/
def brainpoolp384r1R (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) : RfcCurve where
  C := brainpoolp384r1Core hL
  w := 6
  big := false
  sizes := brainpoolp384r1_sizes
  sh := 0
  sh_eq := brainpoolp384r1_sh

/-- `vg_ecdsa_brainpoolp384r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp384r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs) :
    Verified PPC64LE.target (signCodeT (brainpoolp384r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1 vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ brainpoolp384r1_blk rfl hv (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
