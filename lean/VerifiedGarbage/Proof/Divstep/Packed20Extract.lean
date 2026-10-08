import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Signed coefficient extraction for the 20/19-step packed divstep rows. -/
namespace VG.Proof.Divstep

private theorem row_small {n a b : Nat} {u v : Int}
    (ha : a < 2^20) (hb : b < 2^20) (h : |u|+|v| ≤ (2:Int)^n) :
    -(2:Int)^n * 2^20 ≤ u*a+v*b ∧ u*a+v*b < (2:Int)^n*2^20 := by
  have ha0 : (0:Int) ≤ a := Nat.cast_nonneg a
  have hb0 : (0:Int) ≤ b := Nat.cast_nonneg b
  have ha1 : (a:Int) ≤ 2^20-1 := by norm_num at ha ⊢; omega
  have hb1 : (b:Int) ≤ 2^20-1 := by norm_num at hb ⊢; omega
  have hu := abs_nonneg u
  have hv := abs_nonneg v
  have u0 := neg_abs_le u
  have u1 := le_abs_self u
  have v0 := neg_abs_le v
  have v1 := le_abs_self v
  have a0 := mul_le_mul_of_nonneg_right u0 ha0
  have a1 := mul_le_mul_of_nonneg_right u1 ha0
  have b0 := mul_le_mul_of_nonneg_right v0 hb0
  have b1 := mul_le_mul_of_nonneg_right v1 hb0
  have ua := mul_le_mul_of_nonneg_left ha1 hu
  have vb := mul_le_mul_of_nonneg_left hb1 hv
  have hn : (0:Int) < 2^n := pow_pos (by norm_num) _
  constructor <;> linarith only [a0,a1,b0,b1,ua,vb,h,hn]

private theorem row_decompose {n a b : Nat} {u v : Int} (hn : n=19 ∨ n=20) :
    (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n =
      (u*a+v*b)/2^n-u*2^(41-n)-v*2^(62-n) := by
  simp only [mul_sub]
  rcases hn with rfl | rfl <;> norm_num
  all_goals omega

/-- The exact integer decomposition used by both signed extractions. -/
theorem packed20_row {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v| ≤ (2:Int)^n) :
    let l := (u*a+v*b)/2^n;
    -(2:Int)^20 ≤ l ∧ l<2^20 ∧
    (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n = l-u*2^(41-n)-v*2^(62-n) := by
  dsimp only
  obtain ⟨hl,hh⟩ := row_small ha hb h
  have hp : (0:Int)<2^n := pow_pos (by norm_num) _
  refine ⟨?_,?_,row_decompose hn⟩
  · exact (Int.le_ediv_iff_mul_le hp).2 (by nlinarith)
  · exact (Int.ediv_lt_iff_lt_mul hp).2 (by nlinarith)

/-- Recover the negated low coefficient from the packed signed row. -/
theorem packed20_extract_low {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v| ≤ (2:Int)^n) (hu : -(2:Int)^(n-1) ≤ u) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n;
    ((z+2^20)/2^(41-n)+2^20)%2^21-2^20 = -u := by
  obtain ⟨hl,hh,hz⟩ := packed20_row hn ha hb h
  have hub : u ≤ (2:Int)^n := le_trans (le_abs_self u) (by linarith [abs_nonneg v])
  dsimp only
  rw [hz]
  rcases hn with rfl | rfl <;> norm_num at *
  all_goals omega

/-- Recover the negated high coefficient with the signed arithmetic shift. -/
theorem packed20_extract_high {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v| ≤ (2:Int)^n) (hu : -(2:Int)^(n-1) ≤ u) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n;
    (z+2^20+2^41)/2^(62-n) = -v := by
  obtain ⟨hl,hh,hz⟩ := packed20_row hn ha hb h
  have hub : u ≤ (2:Int)^n := le_trans (le_abs_self u) (by linarith [abs_nonneg v])
  dsimp only
  rw [hz]
  rcases hn with rfl | rfl <;> norm_num at *
  all_goals omega

/-- Packed rows fit in a signed word before coefficient extraction. -/
theorem packed20_row_signed {n a b : Nat} {u v : Int}
    (hn : n=19 ∨ n=20) (ha : a<2^20) (hb : b<2^20)
    (h : |u|+|v| ≤ (2:Int)^n) :
    let z := (u*((a:Int)-2^41)+v*((b:Int)-2^62))/2^n;
    -(2:Int)^63 ≤ z ∧ z<2^63 := by
  obtain ⟨hl,hh,hz⟩ := packed20_row hn ha hb h
  have hu := abs_le.mp (le_trans (le_add_of_nonneg_right (abs_nonneg v)) h)
  have hv := abs_le.mp (le_trans (le_add_of_nonneg_left (abs_nonneg u)) h)
  dsimp only
  rw [hz]
  rcases hn with rfl | rfl <;> norm_num at *
  all_goals omega

end VG.Proof.Divstep
