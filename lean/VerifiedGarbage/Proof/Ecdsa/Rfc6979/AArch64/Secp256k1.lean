module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: secp256k1

secp256k1 as the proof's curve (`secp256k1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_secp256k1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at secp256k1's sizes,
which is `Proof.Ecdsa.AArch64.Secp256k1.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem empty_disjoint (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  omega

theorem coreK_secp256k1 : coreK Impl.Ecdsa.AArch64.secp256k1 =
    Proof.Ecdsa.AArch64.Secp256k1.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.secp256k1,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    empty_disjoint, and_true, Proof.Ecdsa.AArch64.Secp256k1.signAArch64]
  rfl

/-! ## The blocks for each hash function's sizes -/

theorem secp256k1_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 16 64) := by rfcT_decide
theorem secp256k1_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 20 64) := by rfcT_decide
theorem secp256k1_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 28 64) := by rfcT_decide
theorem secp256k1_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 32 64) := by rfcT_decide
theorem secp256k1_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 48 128) := by rfcT_decide
theorem secp256k1_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 64 128) := by rfcT_decide
theorem secp256k1_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 28 128) := by rfcT_decide
theorem secp256k1_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.secp256k1 false 0 32 128) := by rfcT_decide

/-- secp256k1, with the group law `hL`, the inversions' soundness `hI`. -/
def secp256k1 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.secp256k1
  inst := Spec.Ecdsa.Secp256k1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.Secp256k1.secp256k1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.Secp256k1.secp256k1_sh
  coreN := "vg_ecdsa_secp256k1_sign_k"
  coreC := Impl.Ecdsa.AArch64.signSecp256k1
  coreX := by rw [coreK_secp256k1]; exact Proof.Ecdsa.AArch64.Secp256k1.sign_a64 hL hI
  coreCT := by rw [coreK_secp256k1]; exact Proof.Ecdsa.AArch64.Secp256k1.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  blkT := blkT_of secp256k1_blk₀ secp256k1_blk₁ secp256k1_blk₂ secp256k1_blk₃ secp256k1_blk₄ secp256k1_blk₅ secp256k1_blk₆ secp256k1_blk₇


theorem secp256k1_tbl : Impl.Ecdsa.AArch64.secp256k1.tbl = [] := rfl

/-- `vg_ecdsa_secp256k1_sign`, with the tables of `vs`. -/
theorem secp256k1T_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) (h : OK vs) :
    Verified AArch64.target (signCode (secp256k1 hL hI) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vs) (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 [] vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.secp256k1 = [] := by simp only [constsOf, secp256k1_tbl, List.isEmpty_nil, ite_true]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.secp256k1 (constsOf Impl.Ecdsa.AArch64.secp256k1) vs).pre s := by
    rw [e]; exact sat_nil h (by decide) rfl
  rw [← e]
  exact signT_verified (R := secp256k1 hL hI) ⟨rfl, by decide, by decide⟩ (.inr secp256k1_tbl) rfl h hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
