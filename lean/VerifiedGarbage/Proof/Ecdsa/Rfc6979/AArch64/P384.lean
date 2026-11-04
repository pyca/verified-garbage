module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Tables
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Tables
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-!
# Deterministic ECDSA on AArch64: P-384

P-384 as the proof's curve (`p384`): scalars of 6 words, the order `n` of
exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-384's sizes, which is `Proof.Ecdsa.AArch64.P384.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The blocks for each hash function's sizes -/

theorem p384_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 16 64) := by rfcT_decide
theorem p384_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 20 64) := by rfcT_decide
theorem p384_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 28 64) := by rfcT_decide
theorem p384_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 32 64) := by rfcT_decide
theorem p384_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 48 128) := by rfcT_decide
theorem p384_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 64 128) := by rfcT_decide
theorem p384_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 28 128) := by rfcT_decide
theorem p384_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.p384 false 0 32 128) := by rfcT_decide

/-- P-384, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP384
  coreX := Proof.Ecdsa.AArch64.P384.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P384.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p384_blk₀ p384_blk₁ p384_blk₂ p384_blk₃ p384_blk₄ p384_blk₅ p384_blk₆ p384_blk₇


theorem p384_tbl : Impl.Ecdsa.AArch64.p384.tbl.isEmpty = false := rfl

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`. -/
theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ Impl.Ecdsa.AArch64.p384.tsym ∉ Proof.HashTable.AArch64.names vs) :
    Verified AArch64.target (signCode (p384 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.AArch64.p384.combConsts vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.p384 = Impl.Ecdsa.AArch64.p384.combConsts := by
    simp only [constsOf, p384_tbl, Bool.false_eq_true, ite_false]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.p384 (constsOf Impl.Ecdsa.AArch64.p384) vs).pre s := by
    rw [e]
    exact sat_one h.1 Proof.Ecdsa.AArch64.P384.satMem h.2 (by rw [Proof.Ecdsa.AArch64.P384.p384_combWords_length]; decide)
      Proof.Ecdsa.AArch64.P384.satMem_held (by decide) rfl
  rw [← e]
  exact signT_verified (R := p384 hL hI hT) ⟨rfl, by decide, by decide⟩ (.inl p384_tbl) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
