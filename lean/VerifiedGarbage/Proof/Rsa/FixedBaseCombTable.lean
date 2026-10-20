module

import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Spec.Rsa

/-! Uniform canonical table blocks and the five-tooth subset recurrence. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa (toWords powMod)
open VG.Spec.Rsa.FixedBaseComb (rows exponent table)

theorem toWords_length (x w : Nat) : (toWords x w).length = w := by
  simp only [toWords,List.length_map,List.length_range]

private theorem blocks_length {α : Type} (f : Nat → List α) (w : Nat)
    (size : ∀ i, (f i).length=w) (l : List Nat) : (l.flatMap f).length=l.length*w := by
  induction l with
  | nil => simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | cons i l ih => simp only [List.flatMap_cons,List.length_append,size,ih,List.length_cons,Nat.succ_mul]; omega

private theorem blocks_slice {α : Type} (f : Nat → List α) (w : Nat)
    (size : ∀ i, (f i).length=w) (l : List Nat) (i : Nat) (hi : i<l.length) :
    ((l.flatMap f).drop (i*w)).take w = f l[i] := by
  induction l generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul,List.drop_zero,List.flatMap_cons,List.getElem_cons_zero]
      rw [← size a,List.take_left]
    | succ i =>
      have pos : i<l.length := by simp only [List.length_cons] at hi; omega
      rw [List.flatMap_cons,Nat.succ_mul,List.drop_append,size]
      rw [List.drop_eq_nil_of_le (by rw [size]; omega),List.nil_append]
      rw [show i*w+w-w=i*w by omega]
      exact ih i pos

theorem table_length (p g bits w : Nat) : (table p g bits w).length=32*w := by
  exact (blocks_length _ w (fun _ => toWords_length _ _) _).trans (by rfl)

theorem table_entry (p g bits w a : Nat) (ha : a<32) :
    ((table p g bits w).drop (a*w)).take w =
      toWords (powMod g (exponent bits a) p * 2^(64*w)%p) w := by
  unfold table
  have h := blocks_slice (fun digit => toWords (powMod g (exponent bits digit) p * 2^(64*w)%p) w)
    w (fun _ => toWords_length _ _) (List.range 32) a (by simpa only [List.length_range] using ha)
  simpa only [List.getElem_range,VG.Spec.Rsa.FixedBaseComb.entries,VG.Spec.Rsa.FixedBaseComb.teeth] using h

theorem exponent_zero (bits : Nat) : exponent bits 0 = 0 := by
  simp only [exponent,VG.Spec.Rsa.FixedBaseComb.teeth,List.range_succ,List.range_zero,
    List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil,
    Nat.zero_div,Nat.zero_mod,Nat.zero_mul,Nat.add_zero]

theorem exponent_add_tooth (bits j low : Nat) (hj : j<5) (hlow : low<2^j) :
    exponent bits (2^j+low) = exponent bits low + 2^(j*rows bits) := by
  have coeff (k : Nat) (hk : k<5) :
      (2^j+low)/2^k%2 = low/2^k%2 + if k=j then 1 else 0 := by
    have jc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    have kc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
    rcases jc with rfl|rfl|rfl|rfl|rfl <;>
      rcases kc with rfl|rfl|rfl|rfl|rfl <;>
      simp only [Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,
        show 2^4=16 from rfl,Nat.div_one,Nat.reduceEqDiff,↓reduceIte] at * <;> omega
  simp only [exponent,VG.Spec.Rsa.FixedBaseComb.teeth,List.range_succ,List.range_zero,
    List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [coeff 0 (by decide),coeff 1 (by decide),coeff 2 (by decide),coeff 3 (by decide),coeff 4 (by decide)]
  have jc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases jc with rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.reduceEqDiff,↓reduceIte] <;>
    simp only [Nat.add_mul,Nat.zero_mul,Nat.zero_add,Nat.one_mul] <;> ac_rfl

theorem exponent_tooth (bits j : Nat) (hj : j<5) :
    exponent bits (2^j) = 2^(j*rows bits) := by
  simpa only [Nat.add_zero,exponent_zero,Nat.zero_add] using
    exponent_add_tooth bits j 0 hj (Nat.two_pow_pos j)

end VG.Proof.Rsa.FixedBaseComb
