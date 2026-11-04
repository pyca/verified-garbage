module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Tables
public import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Tables
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes,
which is `Proof.Ecdsa.AArch64.BrainpoolP256r1.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem empty_disjoint (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  omega

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg =
    Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.signAArch64 := by rfl

/-! ## The blocks for each hash function's sizes -/

theorem brainpoolp256r1_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 16 64) := by rfcT_decide
theorem brainpoolp256r1_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 20 64) := by rfcT_decide
theorem brainpoolp256r1_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 28 64) := by rfcT_decide
theorem brainpoolp256r1_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 32 64) := by rfcT_decide
theorem brainpoolp256r1_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 48 128) := by rfcT_decide
theorem brainpoolp256r1_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 64 128) := by rfcT_decide
theorem brainpoolp256r1_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 28 128) := by rfcT_decide
theorem brainpoolp256r1_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0 32 128) := by rfcT_decide

/-- brainpoolp256r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of brainpoolp256r1_blk₀ brainpoolp256r1_blk₁ brainpoolp256r1_blk₂ brainpoolp256r1_blk₃ brainpoolp256r1_blk₄ brainpoolp256r1_blk₅ brainpoolp256r1_blk₆ brainpoolp256r1_blk₇


theorem brainpoolp256r1_tbl : Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.tbl.isEmpty = false := rfl

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.tsym ∉ Proof.HashTable.AArch64.names vs) :
    Verified AArch64.target (signCode (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg = Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts := by
    simp only [constsOf, brainpoolp256r1_tbl, Bool.false_eq_true, ite_false]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 (constsOf Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg) vs).pre s := by
    rw [e]
    exact sat_one h.1 Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem h.2 (by rw [Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.combCfg_combWords_length]; decide)
      Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem_held (by decide) rfl
  rw [← e]
  exact signT_verified (R := brainpoolp256r1 hL hI) ⟨rfl, by decide, by decide⟩ (.inl brainpoolp256r1_tbl) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
