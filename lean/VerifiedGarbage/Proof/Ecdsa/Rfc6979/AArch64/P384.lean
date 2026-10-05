import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified

/-!
# Deterministic ECDSA on AArch64: P-384

P-384 as the proof's curve (`p384`): scalars of 6 words, the order `n` of
exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-384's sizes, which is `Proof.Ecdsa.AArch64.P384.signAArch64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- P-384, with the group law `hL`, the inversions' last step `hI` and the comb's tables `hT`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.InvToM)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  n46 := .inr rfl
  len := rfl
  nBits := p384_nBits
  n_lt := by decide +kernel
  lt_2n := by decide +kernel
  coreN := Spec.Ecdsa.P384.signApi.name
  coreC := Impl.Ecdsa.AArch64.signP384
  coreX := Proof.Ecdsa.AArch64.P384.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P384.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := ⟨_, by taint_decide⟩
  reduceKeepsV := by decide +kernel

end VG.Proof.Ecdsa.Rfc6979.AArch64
