import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified

/-!
# Deterministic ECDSA on AArch64: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 words, the
order `n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`,
proven correct (given the group law, the inversions' soundness and the comb's
tables) and constant time against its contract (`coreK` at P-224's sizes,
which is `Proof.Ecdsa.AArch64.P224.signAArch64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-- P-224, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, rfl⟩, Proof.Ecdsa.AArch64.P224.p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.P224.p224_sh
  coreN := Spec.Ecdsa.P224.signApi.name
  coreC := Impl.Ecdsa.AArch64.signP224
  coreX := Proof.Ecdsa.AArch64.P224.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P224.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceKeepsV := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.AArch64
