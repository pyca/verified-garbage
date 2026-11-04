module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: p192

p192 as the proof's curve (`p192`): scalars of 24 bytes in 4 words, the
order `n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at p192's sizes,
which is `Proof.Ecdsa.AArch64.P192.signAArch64`).
-/

@[expose] public section

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

/-! ## The blocks for each hash function's sizes -/

theorem p192_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 16 64) := by rfcT_decide
theorem p192_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 20 64) := by rfcT_decide
theorem p192_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 28 64) := by rfcT_decide
theorem p192_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 32 64) := by rfcT_decide
theorem p192_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 48 128) := by rfcT_decide
theorem p192_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 64 128) := by rfcT_decide
theorem p192_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 28 128) := by rfcT_decide
theorem p192_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.p192 false 0 32 128) := by rfcT_decide

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
  coreN := "vg_ecdsa_p192_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP192
  coreX := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_a64 hL hI
  coreCT := by rw [coreK_p192]; exact Proof.Ecdsa.AArch64.P192.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p192_blk₀ p192_blk₁ p192_blk₂ p192_blk₃ p192_blk₄ p192_blk₅ p192_blk₆ p192_blk₇


theorem p192_tbl : Impl.Ecdsa.AArch64.p192.tbl = [] := rfl

/-- `vg_ecdsa_p192_sign`, with the tables of `vs`. -/
theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) (h : OK vs) :
    Verified AArch64.target (signCode (p192 hL hI) Spec.Ecdsa.Rfc6979.Curves.p192.tries vs) (specK Spec.Ecdsa.Rfc6979.Curves.p192 [] vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.p192 = [] := by simp only [constsOf, p192_tbl, List.isEmpty_nil, ite_true]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.p192 (constsOf Impl.Ecdsa.AArch64.p192) vs).pre s := by
    rw [e]; exact sat_nil h (by decide) rfl
  rw [← e]
  exact signT_verified (R := p192 hL hI) ⟨rfl, by decide, by decide⟩ (.inr p192_tbl) rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
