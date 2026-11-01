module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: brainpoolP384r1

brainpoolp384r1 as the proof's curve (`brainpoolp384r1`): scalars of 48 bytes in 6 words, the
order `n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_brainpoolp384r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP384r1's sizes,
which is `Proof.Ecdsa.AArch64.BrainpoolP384r1.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem brainpoolp384r1_empty_disjoint (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  omega

theorem coreK_brainpoolp384r1 : coreK Impl.Ecdsa.AArch64.brainpoolp384r1 =
    Proof.Ecdsa.AArch64.BrainpoolP384r1.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.brainpoolp384r1,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    brainpoolp384r1_empty_disjoint, and_true, Proof.Ecdsa.AArch64.BrainpoolP384r1.signAArch64]
  rfl

/-- brainpoolp384r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp384r1 (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.brainpoolp384r1
  inst := Spec.Ecdsa.BrainpoolP384r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP384r1.brainpoolp384r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.BrainpoolP384r1.brainpoolp384r1_sh
  coreN := "vg_ecdsa_brainpoolp384r1_sign"
  coreC := Impl.Ecdsa.AArch64.signBrainpoolP384r1
  coreX := by rw [coreK_brainpoolp384r1]; exact Proof.Ecdsa.AArch64.BrainpoolP384r1.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp384r1]; exact Proof.Ecdsa.AArch64.BrainpoolP384r1.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  reduceKeepsV := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.AArch64
