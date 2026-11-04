module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothContract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified

/-!
# Deterministic ECDSA on AArch64: P-256

P-256 as the proof's curve (`p256`): scalars of 4 words, the order `n` of
exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-256's sizes, which is `Proof.Ecdsa.AArch64.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-! ## The blocks for each hash function's sizes -/

theorem p256_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 16 64) := by rfcT_decide
theorem p256_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 20 64) := by rfcT_decide
theorem p256_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 28 64) := by rfcT_decide
theorem p256_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 32 64) := by rfcT_decide
theorem p256_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 48 128) := by rfcT_decide
theorem p256_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 64 128) := by rfcT_decide
theorem p256_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 28 128) := by rfcT_decide
theorem p256_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.p256 false 0 32 128) := by rfcT_decide

/-- P-256, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.P256.Booth.sign
  coreX := Proof.Ecdsa.AArch64.booth_sign_a64 hL hI (Proof.Ecdsa.AArch64.booth_comb_correct hL hI hT)
  coreCT := Proof.Ecdsa.AArch64.booth_sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of p256_blk₀ p256_blk₁ p256_blk₂ p256_blk₃ p256_blk₄ p256_blk₅ p256_blk₆ p256_blk₇

theorem p256_tbl : Impl.Ecdsa.AArch64.p256.tbl.isEmpty = false := rfl

/-- `vg_ecdsa_p256_sign`, with the tables of `vs`. -/
theorem p256T_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ Impl.Ecdsa.AArch64.p256.tsym ∉ Proof.HashTable.AArch64.names vs) :
    Verified AArch64.target (signCode (p256 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Ecdsa.AArch64.p256.combConsts vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.p256 = Impl.Ecdsa.AArch64.p256.combConsts := by
    simp only [constsOf, p256_tbl, Bool.false_eq_true, ite_false]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.p256 (constsOf Impl.Ecdsa.AArch64.p256) vs).pre s := by
    rw [e]
    exact sat_one h.1 Proof.Ecdsa.AArch64.satMem h.2 (by rw [Proof.Ecdsa.AArch64.p256_combWords_length]; decide)
      Proof.Ecdsa.AArch64.satMem_held (by decide) rfl
  rw [← e]
  exact signT_verified (R := p256 hL hI hT) ⟨rfl, by decide, by decide⟩ (.inl p256_tbl) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
