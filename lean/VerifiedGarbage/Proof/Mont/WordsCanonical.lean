module

public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Canonical word lists are determined by the arithmetic value of memory. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem wordsVal_word {m : Mem} {base : Addr} {o n j : Nat} (hj : j<n) :
    wordsVal m base o n / 2^(64*j) % 2^64=(word m base (o+8*j)).toNat := by
  induction j generalizing o n with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [Nat.mul_zero,Nat.add_zero,Nat.pow_zero,Nat.div_one,wordsVal]
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (word m base o).isLt]
  | succ j ih =>
    cases n with
    | zero => omega
    | succ n =>
      rw [wordsVal,pow64_succ,←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ (by decide),
        Nat.div_eq_of_lt (word m base o).isLt,Nat.zero_add,ih (by omega)]
      congr 2; omega

theorem wordsAt_canonical (m : Mem) (base : Addr) (o n : Nat) :
    Spec.Rsa.wordsAt m (off base o) n=Spec.Rsa.toWords (wordsVal m base o n) n := by
  unfold Spec.Rsa.wordsAt Spec.Rsa.toWords
  apply List.map_congr_left
  intro j hj
  have h : j<n := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,wordsVal_word h]
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc]

/-- Concatenating adjacent memory ranges concatenates their word lists. -/
theorem wordsAt_append (m : Mem) (base : Addr) (o a b : Nat) :
    Spec.Rsa.wordsAt m (off base o) (a+b)=
      Spec.Rsa.wordsAt m (off base o) a ++ Spec.Rsa.wordsAt m (off base (o+8*a)) b := by
  simp only [Spec.Rsa.wordsAt,List.range_add,List.map_append,List.map_map]
  apply congrArg (List.append _)
  apply List.map_congr_left
  intro j _
  apply congrArg (fun a => m.readW a 64)
  simp only [off,Nat.mul_add,BitVec.ofNat_add]
  ac_rfl

theorem wordsAt_blocks (m : Mem) (base : Addr) (o n count : Nat) :
    Spec.Rsa.wordsAt m (off base o) (count*n)=
      (List.range count).flatMap (fun j => Spec.Rsa.wordsAt m (off base (o+8*n*j)) n) := by
  induction count with
  | zero => simp only [Nat.zero_mul,Spec.Rsa.wordsAt,List.range_zero,List.map_nil,List.flatMap_nil]
  | succ count ih =>
    rw [Nat.succ_mul,wordsAt_append,ih,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [show o+8*(count*n)=o+8*n*count by ac_rfl]

theorem wordsVal_digits {m : Mem} {base : Addr} {o n x : Nat}
    (digits : ∀ j<n, (word m base (o+8*j)).toNat=x/2^(64*j)%2^64) :
    wordsVal m base o n=x%2^(64*n) := by
  induction n with
  | zero => simp only [wordsVal,Nat.mul_zero,Nat.pow_zero,Nat.mod_one]
  | succ n ih =>
    rw [wordsVal_succ_top,ih (fun j hj => digits j (by omega)),digits n (by omega),
      Nat.mul_succ,Nat.pow_add,Nat.mod_mul]

theorem wordsAt_value {m : Mem} {base : Addr} {o n x : Nat}
    (H : Spec.Rsa.wordsAt m (off base o) n=Spec.Rsa.toWords x n) :
    wordsVal m base o n=x%2^(64*n) := by
  apply wordsVal_digits
  intro j hj
  unfold Spec.Rsa.wordsAt Spec.Rsa.toWords at H
  have wordEq := List.map_inj_left.mp H j (List.mem_range.mpr hj)
  have V := congrArg BitVec.toNat wordEq
  simpa only [word,off,BitVec.ofNat_add,BitVec.add_assoc,BitVec.toNat_ofNat] using V

theorem wordsAt_slice (m : Mem) (base : Addr) (o total a b : Nat) (ha : a+b≤total) :
    ((Spec.Rsa.wordsAt m (off base o) total).drop a).take b=
      Spec.Rsa.wordsAt m (off base (o+8*a)) b := by
  have split : total=a+(b+(total-a-b)) := by omega
  rw [split,wordsAt_append,wordsAt_append]
  rw [List.drop_left' (by simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range])]
  exact List.take_left' (by simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range])

end VG.Proof.Mont
