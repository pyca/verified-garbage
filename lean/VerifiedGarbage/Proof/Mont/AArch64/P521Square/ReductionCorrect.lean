module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Spec.Weierstrass

@[expose] public section
set_option exponentiation.threshold 1024
namespace VG.Proof.Mont.AArch64.P521Square

theorem montBase_power : montBase = 2^576 := by decide +kernel

theorem addWords_length (xs ys : List Word) (c : Bool) (h : xs.length = ys.length) :
    (addWords xs ys c).1.length = xs.length := by
  induction xs generalizing ys c with
  | nil => cases ys <;> simp_all [addWords]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simpa [addWords] using ih ys (VG.Proof.Ed25519.Word64.carryOut x y c) (by simpa using h)

theorem value_ones (n : Nat) : value (List.replicate n (~~~(0 : Word))) + 1 = 2^(64*n) := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    simp only [List.replicate_succ, value, Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have he : (~~~(0 : Word)).toNat = 2^64-1 := rfl
    rw [he, Nat.mul_comm (2^(64*n)) (2^64)]
    omega

theorem list9_split (xs : List Word) (h : xs.length = 9) :
    xs = xs.take 8 ++ [xs.getD 8 0] := by
  have h8 : 8 < xs.length := by omega
  have he := List.take_append_drop 8 xs
  rw [List.drop_eq_getElem_cons h8] at he
  have hd : xs.drop 9 = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp only [hd] at he
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h8, Option.getD_some] using he.symm

theorem maskLast_value (xs : List Word) (h : xs.length = 9) :
    value (xs.take 8 ++ [xs.getD 8 0 &&& BitVec.ofNat 64 511]) = value xs % 2^521 := by
  have hv := value_append (xs.take 8) [xs.getD 8 0]
  rw [← list9_split xs h] at hv
  have ht : (xs.take 8).length = 8 := by simp [h]
  have hb := value_lt (xs.take 8)
  rw [ht] at hb hv
  rw [value_append, ht]
  simp only [value, Nat.mul_zero, Nat.add_zero, mask9_value] at hv ⊢
  omega

theorem corrected_value (w : Nat → Word) (hu : inputValue w < fieldPrime*fieldPrime) :
    value (corrected (folded w).1 (folded w).2) = inputValue w % fieldPrime := by
  let xs := (folded w).1
  let c := (folded w).2
  let r := addWords xs (List.replicate 9 (~~~(0 : Word))) c
  have hl : xs.length = 9 := addWords_length _ _ _ rfl
  have hr : r.1.length = 9 := (addWords_length _ _ _ (by simpa using hl)).trans hl
  have ha := addWords_value xs (List.replicate 9 (~~~(0 : Word))) c (by simpa using hl)
  rw [hl] at ha
  have ho := value_ones 9
  have hf := folded_value w
  have hv := value_lt xs
  have hw := value_lt r.1
  rw [hl] at hv
  rw [hr] at hw
  rw [show 64*9=576 by decide] at hv hw
  have ev : value xs + montBase*c.toNat =
      inputValue w % fieldBase + inputValue w / fieldBase + 1 + montBase - fieldBase := by
    change _ + _ = _ at hf
    dsimp only [xs, c, montBase, fieldBase] at *
    omega
  have ew : value r.1 + 1 = value xs + c.toNat + montBase*(1-r.2.toNat) := by
    have hc := Bool.toNat_le r.2
    change value r.1 + 2^(64*9)*r.2.toNat = value xs + _ + c.toNat at ha
    dsimp only [montBase]
    omega
  have h := carry_correction (s := inputValue w % fieldBase + inputValue w / fieldBase)
    (v := value xs) (w := value r.1) (c := c.toNat) (b := 1-r.2.toNat) (fold_sum_bound hu) (Bool.toNat_le c)
    (by omega : 1-r.2.toNat ≤ 1) (by rw [montBase_power]; exact hv)
    (by rw [montBase_power]; exact hw) ev ew
  rw [corrected, maskLast_value _ hr]
  exact h.1.trans (canonical_fold hu).2

end VG.Proof.Mont.AArch64.P521Square
