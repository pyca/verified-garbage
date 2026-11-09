module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Comb
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.Comb
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Deterministic ECDSA on PPC64LE: brainpoolP512r1

Its signature with a given `k` (`brainpoolp512r1Core`), as the proof's curve (`brainpoolp512r1R`), the
taint checks of the blocks that depend on it (`brainpoolp512r1_blk`), and the signature
with the HMAC of a table (`brainpoolp512r1T_verified`). -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- `vg_ecdsa_brainpoolp512r1_sign`, with `[k]G` by the comb, and brainpoolP512r1's group law `hL`. -/
def brainpoolp512r1Core (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : Core where
  E := Spec.Ecdsa.BrainpoolP512r1.inst
  cs := Impl.Weierstrass.PPC64LE.brainpoolp512r1CombConsts
  C := Impl.Ecdsa.PPC64LE.signBrainpoolP512r1Comb
  N := "vg_ecdsa_brainpoolp512r1_sign_k"
  V := (Proof.Ecdsa.PPC64LE.BrainpoolP512r1.combSign_verified hL).1
  ct := (Proof.Ecdsa.PPC64LE.BrainpoolP512r1.combSign_verified hL).2.1
  d := by lit_decide

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The curve's blocks, and the signature with the HMAC of a table -/

theorem brainpoolp512r1_sizes : (Spec.BrainpoolP512r1.curve.len = 24 ∨ Spec.BrainpoolP512r1.curve.len = 28 ∨ Spec.BrainpoolP512r1.curve.len = 32 ∨ Spec.BrainpoolP512r1.curve.len = 48 ∨ Spec.BrainpoolP512r1.curve.len = 64) ∧
    8 = (Spec.BrainpoolP512r1.curve.len + 7) / 8 ∧ Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 8 * Spec.BrainpoolP512r1.curve.len ∧ 2 ^ (8 * Spec.BrainpoolP512r1.curve.len) < 2 * Spec.BrainpoolP512r1.curve.n :=
  ⟨by decide, by decide, by rw [brainpoolp512r1_nBits]; decide, by decide +kernel⟩

theorem brainpoolp512r1_sh : 0 = 8 * Spec.BrainpoolP512r1.curve.len - Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve := by rw [brainpoolp512r1_nBits]; decide

theorem brainpoolp512r1_blk : RfcT (cfgC 8 64 false 0 Spec.BrainpoolP512r1.curve.n) := by rfcT_decide

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1R (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  C := brainpoolp512r1Core hL
  w := 8
  big := false
  sizes := brainpoolp512r1_sizes
  sh := 0
  sh_eq := brainpoolp512r1_sh

/-- `vg_ecdsa_brainpoolp512r1_sign`, with the tables of `vs`, meets `TableInstance.signContract`. -/
theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (vs : List Proof.HmacTable.PPC64LE.HVar)
    (hv : OK vs ∧ "VG_BRAINPOOLP512R1_COMB" ∉ Proof.HmacTable.PPC64LE.names vs) :
    Verified PPC64LE.target (signCodeT (brainpoolp512r1R hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 Impl.Weierstrass.PPC64LE.brainpoolp512r1CombConsts vs) :=
  signT_verified ⟨rfl, by decide, by decide⟩ brainpoolp512r1_blk rfl hv.1
    (sat_one hv.1 Proof.BrainpoolP512r1.PPC64LE.combSatMem hv.2
      (by rw [Proof.BrainpoolP512r1.PPC64LE.comb_words_length]; decide) Proof.BrainpoolP512r1.PPC64LE.combSatMem_held (by decide) rfl)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
