import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified

/-!
# Deterministic ECDSA on AArch64: p192

p192 as the proof's curve (`p192`): scalars of 24 bytes in 4 words, the
order `n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at p192's sizes,
which is `Proof.Ecdsa.AArch64.P192.signAArch64`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem empty_disjoint (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  omega

theorem coreK_p192 : coreK Impl.Ecdsa.AArch64.p192 =
    Proof.Ecdsa.AArch64.P192.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.p192,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    empty_disjoint, and_true, Proof.Ecdsa.AArch64.P192.signAArch64]
  rfl

/-- p192, with the group law `hL`, the inversions' soundness `hI`. -/
def p192 (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inr rfl⟩, Proof.Ecdsa.AArch64.P192.p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.P192.p192_sh
  coreN := Spec.Ecdsa.P192.signApi.name
  coreC := Impl.Ecdsa.AArch64.signP192
  coreX := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_a64 hL hI
  coreCT := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := Function.const _ ⟨_, by taint_decide⟩
  reduceKeepsV := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.AArch64
