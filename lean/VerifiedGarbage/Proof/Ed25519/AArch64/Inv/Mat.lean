module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Math
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The inversion's matrix as magnitudes and signs

`mat` leaves each entry `m` of the matrix as `|m|` and the mask of its sign,
and the rows' carries `negN` (`mat_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.X25519.AArch64 (exec_lsr exec_sub_x exec_eor_x exec_and_x exec_add_x exec_movz)
open VG.Impl.Ed25519.AArch64.Divstep (signMag mat)

/-- The mask of a word's sign. -/
def maskN (m : Word) : Word := if m.msb then BitVec.allOnes 64 else 0

theorem mask_eq (m : Word) : (0 : Word) - (m >>> 63) = maskN m := by
  rw [sgn_word, maskN]
  congr 1
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_true_eq]

theorem absN_word (m : Word) : ((m ^^^ maskN m) - maskN m).toNat = absN m := by
  unfold maskN absN
  cases hm : m.msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 : m.toInt = (m.toNat : Int) := by
      have := BitVec.toInt_eq_msb_cond m
      rw [hm] at this
      simpa using this
    have hl := m.isLt
    rw [BitVec.toNat_sub, BitVec.toNat_xor, show (0 : Word).toNat = 0 from rfl, Nat.xor_zero, h1,
      Int.natAbs_natCast]
    omega
  · simp only [↓reduceIte]
    have h1 : m.toInt = (m.toNat : Int) - 2 ^ 64 := by
      have := BitVec.toInt_eq_msb_cond m
      rw [hm] at this
      simpa using this
    have h2 : 2 ^ 63 ≤ m.toNat := by
      rw [BitVec.msb_eq_decide] at hm
      simpa using hm
    have hl := m.isLt
    rw [BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, h1,
      show ((m.toNat : Int) - 2 ^ 64) = -((2 ^ 64 - m.toNat : Nat) : Int) by omega,
      Int.natAbs_neg, Int.natAbs_natCast]
    omega

/-- The magnitude of a word as the code computes it. -/
abbrev absW (m : Word) : Word := (m ^^^ maskN m) - maskN m

theorem negN_word (m : Word) : (absW m &&& maskN m).toNat = negN m := by
  have ha := absN_word m
  unfold negN
  cases hm : m.msb
  · simp only [maskN, hm, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.toNat_and, show (0 : Word).toNat = 0 from rfl, Nat.and_zero]
  · simp only [absW, maskN, hm, ↓reduceIte] at ha ⊢
    rw [BitVec.and_allOnes]; exact ha

theorem signMag_ok (s : State) {m r : Reg} (hz : s.gpr .x12 = 0) (hmr : m ≠ r) (hr12 : r ≠ .x12) :
    WP isa (.block (signMag m r)) s fun t =>
      t.gpr m = absW (s.gpr m) ∧ t.gpr r = maskN (s.gpr m) ∧ Keeps [m, r] s t := by
  apply WP.of_runBlock
  simp only [signMag, runBlock_cons, runStep_some, runBlock_nil, exec_lsr (by decide : 63 < 64),
    exec_sub_x, exec_eor_x, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, hmr, Ne.symm hmr, Ne.symm hr12, hz, ite_true, ite_false,
      BitVec.setWidth_eq, mask_eq]
  · simp only [RegUpd.gpr_write, hmr, Ne.symm hmr, Ne.symm hr12, hz, ite_true, ite_false,
      BitVec.setWidth_eq, mask_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [RegUpd.gpr_write, hr'.1, hr'.2, ite_false]

theorem mat_ok (s : State) :
    WP isa (.block mat) s fun t =>
      t.gpr .x12 = 0 ∧
      t.gpr .x4 = absW (s.gpr .x4) ∧ t.gpr .x14 = maskN (s.gpr .x4) ∧
      t.gpr .x5 = absW (s.gpr .x5) ∧ t.gpr .x15 = maskN (s.gpr .x5) ∧
      t.gpr .x6 = absW (s.gpr .x6) ∧ t.gpr .x16 = maskN (s.gpr .x6) ∧
      t.gpr .x7 = absW (s.gpr .x7) ∧ t.gpr .x17 = maskN (s.gpr .x7) ∧
      t.gpr .x13 = (absW (s.gpr .x4) &&& maskN (s.gpr .x4)) + (absW (s.gpr .x5) &&& maskN (s.gpr .x5)) ∧
      t.gpr .x11 = (absW (s.gpr .x6) &&& maskN (s.gpr .x6)) + (absW (s.gpr .x7) &&& maskN (s.gpr .x7)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  simp only [mat, List.append_assoc]
  rw [WP.block_append_iff]
  have hz : WP isa (.block [.movz .x .x12 0 0]) s fun t => t.gpr .x12 = 0 ∧ Keeps [.x12] s t :=
    WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨RegUpd.gpr_write_self _ _ _ _,
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩
  refine WP.mono hz fun s0 ⟨z0, k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s0 z0 (by decide) (by decide)) fun s1 ⟨m1, r1, k1⟩ => ?_
  have z1 : s1.gpr .x12 = 0 := (k1.gpr _ (by decide)).trans z0
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s1 z1 (by decide) (by decide)) fun s2 ⟨m2, r2, k2⟩ => ?_
  have z2 : s2.gpr .x12 = 0 := (k2.gpr _ (by decide)).trans z1
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s2 z2 (by decide) (by decide)) fun s3 ⟨m3, r3, k3⟩ => ?_
  have z3 : s3.gpr .x12 = 0 := (k3.gpr _ (by decide)).trans z2
  rw [WP.block_append_iff]
  refine WP.mono (signMag_ok s3 z3 (by decide) (by decide)) fun s4 ⟨m4, r4, k4⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_and_x, exec_add_x,
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  -- each register's value, in terms of `s`
  have g0 : ∀ r, r ≠ .x12 → s0.gpr r = s.gpr r := fun r h => k0.gpr r (by simpa using h)
  have e4 : s4.gpr .x4 = absW (s.gpr .x4) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), m1, g0 _ (by decide)]
  have e14 : s4.gpr .x14 = maskN (s.gpr .x4) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), r1, g0 _ (by decide)]
  have e5 : s4.gpr .x5 = absW (s.gpr .x5) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), m2, k1.gpr _ (by decide), g0 _ (by decide)]
  have e15 : s4.gpr .x15 = maskN (s.gpr .x5) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), r2, k1.gpr _ (by decide), g0 _ (by decide)]
  have e6 : s4.gpr .x6 = absW (s.gpr .x6) := by
    rw [k4.gpr _ (by decide), m3, k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e16 : s4.gpr .x16 = maskN (s.gpr .x6) := by
    rw [k4.gpr _ (by decide), r3, k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e7 : s4.gpr .x7 = absW (s.gpr .x7) := by
    rw [m4, k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have e17 : s4.gpr .x17 = maskN (s.gpr .x7) := by
    rw [r4, k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), g0 _ (by decide)]
  have z4 : s4.gpr .x12 = 0 := (k4.gpr _ (by decide)).trans z3
  refine ⟨z4, e4, e14, e5, e15, e6, e16, e7, e17, by rw [e4, e14, e5, e15],
    by rw [e6, e16, e7, e17], ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h7, h8, h9, h11, h12, h13, h14, h15, h16, h17⟩ := hr
    simp only [RegUpd.gpr_write, h8, h9, h11, h13, ite_false]
    rw [k4.gpr r (by simp [h7, h17]), k3.gpr r (by simp [h6, h16]), k2.gpr r (by simp [h5, h15]),
      k1.gpr r (by simp [h4, h14]), g0 r h12]
  · simp only [RegUpd.mem_write]; rw [k4.mem, k3.mem, k2.mem, k1.mem, k0.mem]
  · simp only [RegUpd.rd_write]; rw [k4.rd, k3.rd, k2.rd, k1.rd, k0.rd]
  · simp only [RegUpd.wr_write]; rw [k4.wr, k3.wr, k2.wr, k1.wr, k0.wr]
  · simp only [RegUpd.sp_write]; rw [k4.sp, k3.sp, k2.sp, k1.sp, k0.sp]

end VG.Proof.Ed25519.AArch64.Inv
