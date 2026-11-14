module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsChainMath
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64

theorem cms_carry_zero (x : Word) (c : Bool) : carryOut x 0 c=(decide (x=BitVec.allOnes 64) && c) := by
  have he : x=BitVec.allOnes 64 ↔ x.toNat=2^64-1 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  cases c
  · simp only [Bool.and_false,carryOut,Bool.toNat_false,show (0 : Word).toNat=0 from rfl,Nat.add_zero,decide_eq_false_iff_not]
    exact Nat.not_le.mpr x.isLt
  · simp only [Bool.and_true,carryOut,Bool.toNat_true,show (0 : Word).toNat=0 from rfl,Nat.add_zero]
    apply decide_eq_decide.mpr
    rw [he]
    have hx := x.isLt
    omega_arith

theorem cms_and_carry (a b : Word) (c : Bool) : carryOut (a&&&b) 0 c=carryOut b 0 (carryOut a 0 c) := by
  rw [cms_carry_zero,cms_carry_zero,cms_carry_zero]
  simp only [BitVec.and_eq_allOnes_iff,Bool.decide_and,Bool.and_assoc]
  exact Bool.and_left_comm _ _ _

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsAndWords : List Word → Word
  | [] => BitVec.allOnes 64
  | a::xs => a&&&cmsAndWords xs

theorem cms_allOnes_carry (c : Bool) : carryOut (BitVec.allOnes 64) 0 c=c := by
  rw [cms_carry_zero]
  simp only [decide_true,Bool.true_and]

theorem cms_carry_tail (xs : List Word) (top : Word) (c : Bool) :
    (addWords (xs++[top]) (List.replicate (xs.length+1) 0) c).2=
      carryOut top 0 (carryOut (cmsAndWords xs) 0 c) := by
  induction xs generalizing c with
  | nil =>
    simp only [List.nil_append,List.length_nil,Nat.zero_add,List.replicate_succ,List.replicate_zero,addWords,cmsAndWords,cms_allOnes_carry]
  | cons a xs ih =>
    simp only [List.cons_append,List.length_cons,List.replicate_succ,addWords,cmsAndWords]
    rw [←List.replicate_succ,ih,cms_and_carry]

theorem cms_compressed_carry (lo h top : Word) (xs : List Word) (c : Bool) :
    (addWords (lo::(xs++[top])) (h::List.replicate (xs.length+1) 0) c).2=
      carryOut top 0 (carryOut (cmsAndWords xs) 0 (carryOut lo h c)) := by
  simp only [addWords]
  exact cms_carry_tail xs top (carryOut lo h c)

end VG.Proof.Mont.AArch64.P521Field
