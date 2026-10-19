module
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords

import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square

def shifted55 : List Word → List Word
  | [] => []
  | [x] => [x >>> 55]
  | x::y::ys => ((y ++ x).extractLsb' 55 64) :: shifted55 (y::ys)

theorem extr55 (x y : Word) :
    ((y ++ x).extractLsb' 55 64).toNat = x.toNat / 2^55 + 512 * (y.toNat % 2^55) := by
  rw [extract_toNat]
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem shifted55_value (xs : List Word) :
    value xs = 2^55 * value (shifted55 xs) + (xs.headD 0).toNat % 2^55 := by
  induction xs using shifted55.induct with
  | case1 => simp [shifted55, value]
  | case2 x =>
    simp only [shifted55, value, List.headD_cons, Nat.mul_zero, Nat.add_zero,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  | case3 x y ys ih =>
    simp only [shifted55, value, List.headD_cons, extr55] at *
    omega

theorem orLow9 (x y : Word) (hy : y.toNat < 512) :
    y ||| (x <<< 9) = (x.setWidth 55 ++ y.setWidth 9) := by
  have he : y = (y.setWidth 9).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  rw [he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem orLow9_value (x y : Word) (hy : y.toNat < 512) :
    (y ||| (x <<< 9)).toNat = y.toNat + 512*(x.toNat % 2^55) := by
  rw [orLow9 x y hy, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (y.setWidth 9).isLt]
  simp only [BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

theorem rotated_value (w : Nat → Word)
    (ht : value ((List.range 9).map w) < 2^521) :
    value (rotated w) = value ((List.range 9).map w) / 2^55 +
      2^466*(value ((List.range 9).map w) % 2^55) := by
  have he : (List.range 9).map w = (List.range 8).map w ++ [w 8] := rfl
  have hb := value_lt ((List.range 8).map w)
  have hv := value_append ((List.range 8).map w) [w 8]
  rw [← he] at hv
  simp only [List.length_map, List.length_range, value, Nat.mul_zero, Nat.add_zero] at hv
  have hy : (w 8).toNat < 512 := by omega
  have hs := shifted55_value ((List.range 8).map w ++ [w 8 ||| (w 0 <<< 9)])
  have hm : (value ((List.range 9).map w)) % 2^55 = (w 0).toNat % 2^55 := by
    change ((w 0).toNat + 2^64 * value ((List.range 8).map (fun i => w (i+1)))) % (2^55) = _
    omega
  have hr : shifted55 ((List.range 8).map w ++ [w 8 ||| (w 0 <<< 9)]) = rotated w := rfl
  rw [hr, value_append] at hs
  simp only [List.length_map, List.length_range, value, Nat.mul_zero, Nat.add_zero,
    orLow9_value (w 0) (w 8) hy] at hs
  change _ = 2^55 * value (rotated w) + (w 0).toNat % 2^55 at hs
  rw [hm]
  omega

end VG.Proof.Mont.AArch64.P521Square
