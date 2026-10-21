module
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law

import VerifiedGarbage.Proof.Weierstrass.Comb

/-! Sparse signed nine-bit recoding of a public scalar, its digits (`±1 … ±255`)
stored in sixteen bits (`word`). -/

@[expose] public section

namespace VG.Proof.Weierstrass.FastNaf9
open Spec.Weierstrass

def next (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else ((n + 256) / 512) * 256

def residual (k : Nat) : Nat → Nat
  | 0 => k
  | j + 1 => next (residual k j)

def negative (k j : Nat) : Bool :=
  decide (residual k j % 2 ≠ 0 ∧ 256 ≤ residual k j % 512)

def magnitude (k j : Nat) : Nat :=
  let n := residual k j
  if n % 2 = 0 then 0 else if n % 512 < 256 then n % 512 else 512 - n % 512

def digit (k j : Nat) : Int :=
  if negative k j then -(magnitude k j : Int) else (magnitude k j : Int)

def word (k j : Nat) : BitVec 16 := BitVec.ofInt 16 (digit k j)

theorem residual_zero (k : Nat) : residual k 0 = k := rfl

theorem residual_succ (k j : Nat) : residual k (j+1)=next (residual k j) := rfl

theorem mod512_parity (n : Nat) : n % 512 % 2 = n % 2 := by omega

theorem magnitude_le (k j : Nat) : magnitude k j ≤ 255 := by
  have hr := Nat.mod_lt (residual k j) (by decide : 0<512)
  have hp := mod512_parity (residual k j)
  dsimp only [magnitude]
  split <;> (try split) <;> omega

theorem magnitude_odd_or_zero (k j : Nat) : magnitude k j=0 ∨ magnitude k j%2=1 := by
  have hp := mod512_parity (residual k j)
  have hr := Nat.mod_lt (residual k j) (by decide : 0<512)
  dsimp only [magnitude]
  split <;> (try split) <;> omega

theorem magnitude_zero_iff (k j : Nat) : magnitude k j=0 ↔ residual k j%2=0 := by
  have hp := mod512_parity (residual k j)
  have hr := Nat.mod_lt (residual k j) (by decide : 0<512)
  dsimp only [magnitude]
  split <;> (try split) <;> omega

theorem recurrence (k j : Nat) :
    if negative k j then residual k j + magnitude k j = 2*residual k (j+1)
    else residual k j = 2*residual k (j+1)+magnitude k j := by
  have hd := Nat.div_add_mod (residual k j) 512
  have hr := Nat.mod_lt (residual k j) (by decide : 0<512)
  have hp := mod512_parity (residual k j)
  simp only [negative,magnitude,residual_succ,next]
  by_cases he : residual k j%2=0
  · simp only [he,ne_eq,not_true_eq_false,false_and,decide_false,Bool.false_eq_true,ite_false,ite_true]
    omega
  · simp only [he,ne_eq,not_false_eq_true,true_and,ite_false,decide_eq_true_eq]
    split <;> split <;> omega

theorem negative_magnitude_pos (k j : Nat) (h : negative k j=true) : 0<magnitude k j := by
  have hz := magnitude_zero_iff k j
  simp only [negative,decide_eq_true_eq] at h
  omega

theorem word_toNat (k j : Nat) :
    (word k j).toNat = if negative k j then 65536-magnitude k j else magnitude k j := by
  have hb := magnitude_le k j
  have hp := negative_magnitude_pos k j
  simp only [word,digit,BitVec.toNat_ofInt,Nat.reducePow]
  cases hn : negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((magnitude k j : Int)%65536).toNat=magnitude k j
    omega
  · have hp := hp hn
    simp only [ite_true]
    change ((-(magnitude k j : Int))%65536).toNat=65536-magnitude k j
    omega

theorem word_magnitude (k j : Nat) :
    (if (word k j).toNat<256 then (word k j).toNat else 65536-(word k j).toNat)=magnitude k j := by
  have hb := magnitude_le k j
  have hp := negative_magnitude_pos k j
  rw [word_toNat]
  cases hn : negative k j <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at * <;> split <;> omega

theorem word_negative (k j : Nat) : decide (256≤(word k j).toNat)=negative k j := by
  have hb := magnitude_le k j
  have hp := negative_magnitude_pos k j
  rw [word_toNat]
  cases hn : negative k j <;> simp only [hn,Bool.false_eq_true,ite_false,ite_true] at *
  · exact decide_eq_false (by omega)
  · exact decide_eq_true (by omega)

theorem word_zero_iff (k j : Nat) : word k j=0 ↔ magnitude k j=0 := by
  have hb := magnitude_le k j
  rw [←BitVec.toNat_inj]
  change (word k j).toNat=0 ↔ magnitude k j=0
  rw [word_toNat]
  cases hn : negative k j
  · simp only [Bool.false_eq_true,ite_false]
  · have hp := negative_magnitude_pos k j hn
    simp only [ite_true]
    omega

def byte (k j : Nat) : BitVec 8 := BitVec.ofInt 8 (digit k j)

theorem byte_toNat (k j : Nat) :
    (byte k j).toNat = if negative k j then 256-magnitude k j else magnitude k j := by
  have hb := magnitude_le k j
  have hp := negative_magnitude_pos k j
  simp only [byte,digit,BitVec.toNat_ofInt,Nat.reducePow]
  cases hn : negative k j
  · simp only [Bool.false_eq_true,ite_false]
    change ((magnitude k j : Int)%256).toNat=magnitude k j
    omega
  · have hp := hp hn
    simp only [ite_true]
    change ((-(magnitude k j : Int))%256).toNat=256-magnitude k j
    omega

theorem byte_zero_iff (k j : Nat) : byte k j=0 ↔ magnitude k j=0 := by
  have hb := magnitude_le k j
  rw [←BitVec.toNat_inj]
  change (byte k j).toNat=0 ↔ magnitude k j=0
  rw [byte_toNat]
  cases hn : negative k j
  · simp only [Bool.false_eq_true,ite_false]
  · have hp := negative_magnitude_pos k j hn
    simp only [ite_true]
    omega

theorem digit_mod512 (k j : Nat) : digit k j =
    if residual k j%512%2=0 then 0 else if residual k j%512<256 then (residual k j%512:Int) else (residual k j%512:Int)-512 := by
  have hr := Nat.mod_lt (residual k j) (by decide : 0<512)
  rw [mod512_parity]
  simp only [digit,negative,magnitude,decide_eq_true_eq]
  split <;> split <;> (try split) <;> omega

/-- One recoding step halves any power-of-two bound. -/
theorem next_pow_bound {n e : Nat} (hn : n≤2^(e+1)) : next n≤2^e := by
  by_cases he : n%2=0
  · rw [next,ite_eq_left he,Nat.pow_succ] at *; omega
  · rw [next,ite_eq_right he]
    by_cases h8 : e<8
    · rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceAdd,Nat.reducePow] at hn ⊢ <;> omega
    · have hp : 2^(e+1)=512*2^(e-8) := by
        rw [show 512=2^9 from rfl,←Nat.pow_add]; congr 1; omega
      have hq : 2^e=256*2^(e-8) := by
        rw [show 256=2^8 from rfl,←Nat.pow_add]; congr 1; omega
      rw [hp] at hn
      rw [hq]
      omega

/-- The residual of a scalar of `B` bits after `j` digits has `B - j` bits. -/
theorem residual_boundB {B k : Nat} (hk : k≤2^B) {j : Nat} (hj : j≤B) :
    residual k j≤2^(B-j) := by
  induction j with
  | zero => exact hk
  | succ j ih =>
    have hp := ih (by omega)
    have he : B-j=(B-(j+1))+1 := by omega
    rw [he] at hp
    exact next_pow_bound hp

/-- A scalar of `B` bits has `B + 1` digits. -/
theorem residual_zero_top {B k : Nat} (hk : k<2^B) : residual k (B+1)=0 := by
  have h := residual_boundB (Nat.le_of_lt hk) (j:=B) (by omega)
  simp only [Nat.sub_self,Nat.pow_zero] at h
  change next (residual k B)=0
  unfold next
  split <;> omega

def point (C : Curve) (P : Point C) (k j : Nat) : Point C :=
  if negative k j then negPt (mul (magnitude k j) P) else mul (magnitude k j) P

theorem add_step {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true) (k j : Nat) :
    Spec.Weierstrass.add (mul (2*residual k (j+1)) P) (point C P k j)=mul (residual k j) P := by
  have hs := recurrence k j
  cases he : negative k j with
  | false =>
    simp only [point,he,Bool.false_eq_true,ite_false] at hs ⊢
    rw [hC.add_mul_mul hP]
    congr 1; omega
  | true =>
    simp only [point,he,ite_true] at hs ⊢
    rw [hC.add_mul_neg hP (by omega)]
    congr 1; omega

theorem onCurve_point {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true) (k j : Nat) :
    onCurve C (point C P k j)=true := by
  unfold point
  split
  · exact onCurve_negPt (hC.onCurve_mul hP _)
  · exact hC.onCurve_mul hP _

end VG.Proof.Weierstrass.FastNaf9
