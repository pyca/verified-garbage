module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Tables
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Tables
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 words, the
order `n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`,
proven correct (given the group law, the inversions' soundness and the comb's
tables) and constant time against its contract (`coreK` at P-224's sizes,
which is `Proof.Ecdsa.AArch64.P224.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-! ## The blocks for each hash function's sizes -/

theorem p224_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 16 64) := by rfcT_decide
theorem p224_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 20 64) := by rfcT_decide
theorem p224_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 28 64) := by rfcT_decide
theorem p224_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 32 64) := by rfcT_decide
theorem p224_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 48 128) := by rfcT_decide
theorem p224_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 64 128) := by rfcT_decide
theorem p224_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 28 128) := by rfcT_decide
theorem p224_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.p224 false 0 32 128) := by rfcT_decide

/-- P-224, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inr ⟨rfl, .inl rfl⟩, Proof.Ecdsa.AArch64.P224.p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.P224.p224_sh
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP224
  coreX := Proof.Ecdsa.AArch64.P224.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P224.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p224_blk₀ p224_blk₁ p224_blk₂ p224_blk₃ p224_blk₄ p224_blk₅ p224_blk₆ p224_blk₇


theorem p224_tbl : Impl.Ecdsa.AArch64.p224.tbl.isEmpty = false := rfl

/-- `vg_ecdsa_p224_sign`, with the tables of `vs`. -/
theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ Impl.Ecdsa.AArch64.p224.tsym ∉ Proof.HashTable.AArch64.names vs) :
    Verified AArch64.target (signCode (p224 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 Impl.Ecdsa.AArch64.p224.combConsts vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.p224 = Impl.Ecdsa.AArch64.p224.combConsts := by
    simp only [constsOf, p224_tbl, Bool.false_eq_true, ite_false]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.p224 (constsOf Impl.Ecdsa.AArch64.p224) vs).pre s := by
    rw [e]
    exact sat_one h.1 Proof.Ecdsa.AArch64.P224.satMem h.2 (by rw [Proof.Ecdsa.AArch64.P224.p224_combWords_length]; decide)
      Proof.Ecdsa.AArch64.P224.satMem_held (by decide) rfl
  rw [← e]
  exact signT_verified (R := p224 hL hI hT) ⟨rfl, by decide, by decide⟩ (.inl p224_tbl) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
