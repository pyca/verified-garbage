module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Mont.Words

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square
open VG.Proof.Ed25519.Word64
/-- The natural value of the two-word extract used by both shifts. -/
theorem extract_toNat (n m : Word) (lsb : Nat) :
    ((n ++ m).extractLsb' lsb 64).toNat = (n.toNat * 2^64 + m.toNat) / 2^lsb % 2^64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem value_append (xs ys : List Word) :
    value (xs ++ ys) = value xs + 2^(64*xs.length) * value ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
    simp only [List.cons_append, value, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.pow_add, ih]
    simp only [Nat.mul_assoc, Nat.add_assoc, Nat.mul_left_comm]

theorem addWords_value (xs ys : List Word) (c : Bool) (hl : xs.length = ys.length) :
    value (addWords xs ys c).1 + 2^(64*xs.length) * (addWords xs ys c).2.toNat =
      value xs + value ys + c.toNat := by
  induction xs generalizing ys c with
  | nil => cases ys <;> simp_all [addWords, value]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have h := ih ys (carryOut x y c) (by simpa using hl)
      have hxy := addCarry_value x y c
      simp only [addWords, value, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.pow_add] at *
      rw [Nat.mul_right_comm (2 ^ (64 * xs.length)) (2^64)]
      omega

def shifted9 : List Word → List Word
  | [] => []
  | [x] => [x >>> 9]
  | x::y::ys => ((y ++ x).extractLsb' 9 64) :: shifted9 (y::ys)

theorem extr9 (x y : Word) :
    ((y ++ x).extractLsb' 9 64).toNat = x.toNat / 512 + 2^55 * (y.toNat % 512) := by
  rw [extract_toNat]
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem shifted9_value (xs : List Word) :
    value xs = 512 * value (shifted9 xs) + (xs.headD 0).toNat % 512 := by
  induction xs using shifted9.induct with
  | case1 => simp [shifted9, value]
  | case2 x =>
    simp only [shifted9, value, List.headD_cons, Nat.mul_zero, Nat.add_zero,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  | case3 x y ys ih =>
    simp only [shifted9, value, List.headD_cons, extr9] at *
    omega

end VG.Proof.Mont.AArch64.P521Square
