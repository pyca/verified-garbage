module
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords

import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic

@[expose] public section
set_option exponentiation.threshold 1024
namespace VG.Proof.Mont.AArch64.P521Square

theorem value_lt (xs : List Word) : value xs < 2^(64*xs.length) := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
    have hx := x.isLt
    simp only [value, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [Nat.mul_comm (2^(64*xs.length)) (2^64)]
    omega

def inputValue (w : Nat → Word) : Nat := value ((List.range 17).map w)

theorem input_parts (w : Nat → Word) :
    inputValue w = value ((List.range 8).map w) +
      2^512 * (512*value (foldHigh w) + (w 8).toNat % 512) := by
  have he : (List.range 17).map w = (List.range 8).map w ++
      (List.range 9).map (fun i => w (i+8)) := rfl
  have hv := shifted9_value ((List.range 9).map (fun i => w (i+8)))
  have hs : shifted9 ((List.range 9).map (fun i => w (i+8))) = foldHigh w := rfl
  rw [hs] at hv
  change value ((List.range 9).map (fun i => w (i+8))) =
    512 * value (foldHigh w) + (w 8).toNat % 512 at hv
  rw [inputValue, he, value_append, hv]
  rfl

theorem foldHigh_value (w : Nat → Word) : value (foldHigh w) = inputValue w / 2^521 := by
  have h := input_parts w
  have hlow := value_lt ((List.range 8).map w)
  have hm := Nat.mod_lt (w 8).toNat (by decide : 0 < 512)
  simp only [List.length_map, List.length_range] at hlow
  omega

theorem foldLow_value (w : Nat → Word) :
    value (foldLow w) = inputValue w % 2^521 + (2^576-2^521) := by
  have h := input_parts w
  have hlow := value_lt ((List.range 8).map w)
  have hm := Nat.mod_lt (w 8).toNat (by decide : 0 < 512)
  simp only [List.length_map, List.length_range] at hlow
  simp only [foldLow, value_append, List.length_map, List.length_range, value,
    Nat.mul_zero, Nat.add_zero, orHigh9_value]
  omega

theorem folded_value (w : Nat → Word) :
    value (folded w).1 + 2^576 * (folded w).2.toNat =
      inputValue w % 2^521 + inputValue w / 2^521 + 1 + (2^576-2^521) := by
  have h := addWords_value (foldLow w) (foldHigh w) true (by rfl)
  rw [foldLow_value, foldHigh_value] at h
  have hlen : (foldLow w).length = 9 := rfl
  rw [hlen, show 64*9=576 by decide] at h
  change value (folded w).1 + 2^576 * (folded w).2.toNat =
    inputValue w % 2^521 + (2^576-2^521) + inputValue w / 2^521 + 1 at h
  omega

end VG.Proof.Mont.AArch64.P521Square
