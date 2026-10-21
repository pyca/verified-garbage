module

import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The five public columns reconstruct an exponent and admit a binary Horner scan. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa.FixedBaseComb (rows exponent)

def bit (x k : Nat) : Nat := x / 2 ^ k % 2

def digit (bits x row : Nat) : Nat :=
  bit x row + 2 * bit x (row + rows bits) + 4 * bit x (row + 2 * rows bits) +
    8 * bit x (row + 3 * rows bits) + 16 * bit x (row + 4 * rows bits)

theorem bit_lt (x k : Nat) : bit x k < 2 := Nat.mod_lt _ (by decide)

theorem digit_lt (bits x row : Nat) : digit bits x row < 32 := by
  have := bit_lt x row; have := bit_lt x (row + rows bits)
  have := bit_lt x (row + 2*rows bits); have := bit_lt x (row + 3*rows bits)
  have := bit_lt x (row + 4*rows bits)
  unfold digit
  omega

theorem digit_bit (bits x row j : Nat) (hj : j < 5) :
    digit bits x row / 2 ^ j % 2 = bit x (row + j * rows bits) := by
  have := bit_lt x row; have := bit_lt x (row + rows bits)
  have := bit_lt x (row + 2*rows bits); have := bit_lt x (row + 3*rows bits)
  have := bit_lt x (row + 4*rows bits)
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;>
    simp only [digit, Nat.pow_zero, Nat.pow_one, Nat.div_one, Nat.zero_mul, Nat.add_zero,
      Nat.one_mul, show 2^2=4 from rfl, show 2^3=8 from rfl, show 2^4=16 from rfl] <;> omega

def slice (x start width : Nat) : Nat := x / 2 ^ start % 2 ^ width

def high (bits x row : Nat) : Nat :=
  let d := rows bits
  let b := 2 ^ d
  slice x row (d-row) + b * slice x (row+d) (d-row) +
    b^2 * slice x (row+2*d) (d-row) + b^3 * slice x (row+3*d) (d-row) +
      b^4 * slice x (row+4*d) (d-row)

theorem rows_cover (bits : Nat) : bits ≤ 5 * rows bits := by
  simp only [rows, VG.Spec.Rsa.FixedBaseComb.teeth]
  omega

theorem high_top (bits x : Nat) : high bits x (rows bits) = 0 := by
  simp [high,slice,Nat.mod_one]

theorem slice_step (x start width : Nat) :
    slice x start (width+1) = bit x start + 2 * slice x (start+1) width := by
  simp only [slice,bit,Nat.pow_succ']
  rw [Nat.mod_mul]
  rw [Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm (2^start) 2]

theorem exponent_digit (bits x row : Nat) :
    exponent bits (digit bits x row) =
      bit x row + 2^(rows bits) * bit x (row+rows bits) +
      (2^(rows bits))^2 * bit x (row+2*rows bits) +
      (2^(rows bits))^3 * bit x (row+3*rows bits) +
      (2^(rows bits))^4 * bit x (row+4*rows bits) := by
  simp only [exponent,VG.Spec.Rsa.FixedBaseComb.teeth,List.range_succ,List.range_zero,
    List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [digit_bit _ _ _ 0 (by decide),digit_bit _ _ _ 1 (by decide),
    digit_bit _ _ _ 2 (by decide),digit_bit _ _ _ 3 (by decide),digit_bit _ _ _ 4 (by decide)]
  simp only [Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.pow_zero,Nat.mul_one]
  simp only [Nat.mul_comm 2 (rows bits),Nat.mul_comm 3 (rows bits),Nat.mul_comm 4 (rows bits),Nat.pow_mul]
  ac_rfl

theorem high_step (bits x row : Nat) (hr : row < rows bits) :
    high bits x row = 2 * high bits x (row+1) + exponent bits (digit bits x row) := by
  have width : rows bits-row = (rows bits-(row+1))+1 := by omega
  dsimp only [high]
  rw [width]
  simp only [slice_step]
  rw [exponent_digit]
  have a1 : row + rows bits + 1 = row+1+rows bits := by omega
  have a2 : row + 2*rows bits + 1 = row+1+2*rows bits := by omega
  have a3 : row + 3*rows bits + 1 = row+1+3*rows bits := by omega
  have a4 : row + 4*rows bits + 1 = row+1+4*rows bits := by omega
  rw [a1,a2,a3,a4]
  simp only [Nat.mul_add]
  ac_rfl

private def chunks (x b : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => x%b + b*chunks (x/b) b n

private theorem chunks_eq (x b n : Nat) : chunks x b n = x % b^n := by
  induction n generalizing x with
  | zero => simp [chunks,Nat.mod_one]
  | succ n ih =>
    rw [chunks,ih,Nat.pow_succ',Nat.mod_mul]

theorem high_zero_mod (bits x : Nat) : high bits x 0 = x % 2 ^ (5*rows bits) := by
  let d := rows bits
  let b := 2^d
  have p2 : 2^(2*d)=b^2 := by rw [Nat.mul_comm 2 d,Nat.pow_mul]
  have p3 : 2^(3*d)=b^3 := by rw [Nat.mul_comm 3 d,Nat.pow_mul]
  have p4 : 2^(4*d)=b^4 := by rw [Nat.mul_comm 4 d,Nat.pow_mul]
  have p5 : 2^(5*d)=b^5 := by rw [Nat.mul_comm 5 d,Nat.pow_mul]
  have e := chunks_eq x b 5
  simp only [chunks,Nat.div_div_eq_div_mul,Nat.mul_zero,Nat.add_zero] at e
  simp only [high,Nat.sub_zero,Nat.zero_add]
  change slice x 0 d + b*slice x d d + b^2*slice x (2*d) d +
    b^3*slice x (3*d) d + b^4*slice x (4*d) d = x%2^(5*d)
  simp only [slice,Nat.pow_zero,Nat.div_one,p2,p3,p4,p5]
  change x%b+b*(x/b%b)+b^2*(x/b^2%b)+b^3*(x/b^3%b)+b^4*(x/b^4%b) = x%b^5
  rw [←e]
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_add,Nat.mul_assoc]
  ac_rfl

theorem high_zero (bits x : Nat) (bound : x < 2^bits) : high bits x 0 = x := by
  rw [high_zero_mod,Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (rows_cover bits))

theorem rows_pos {bits : Nat} (positive : 0<bits) : 0<rows bits := by
  unfold rows VG.Spec.Rsa.FixedBaseComb.teeth
  omega

theorem rows_small {bits : Nat} (bound : bits≤8192) : rows bits≤1639 ∧ 6*rows bits<2^31 := by
  unfold rows VG.Spec.Rsa.FixedBaseComb.teeth
  omega

end VG.Proof.Rsa.FixedBaseComb
