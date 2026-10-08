import VerifiedGarbage.Proof.P256.Linear.WeakWords
import VerifiedGarbage.Proof.P256.Linear.Words

namespace VG.Proof.P256.Linear.FortyOne
open VG VG.AArch64 VG.Proof.Ed25519.Word64
open Weak (W4 value addWords subWords addWords_value subWords_value value_lt)

/-- Four low words of multiplication by four, and its high word. -/
def shift2 (a : W4) : W4 × Word :=
  ((a.1 <<< 2,(a.2.1++a.1).extractLsb' 62 64,
    (a.2.2.1++a.2.1).extractLsb' 62 64,
    (a.2.2.2++a.2.2.1).extractLsb' 62 64),a.2.2.2 >>> 62)

theorem shift2_value (a : W4) :
    value (shift2 a).1+radix*(shift2 a).2.toNat=4*value a := by
  have h := leftShift_value 2 (by simp) a.1 a.2.1 a.2.2.1 a.2.2.2
  simp only [five,VerifySparse.four,show 64-2=62 from rfl,show 2^2=4 from rfl] at h
  simp only [shift2,value,val4,radix]
  omega

def highWord (h : Word) (c : Bool) : Word := addCarry h (~~~(0 : Word)) c
def quotient (h : Word) (c : Bool) : Word := highWord h c+1

theorem quotient_value (h : Word) (c : Bool) (hh : h.toNat<4) :
    (quotient h c).toNat=h.toNat+c.toNat := by
  cases c <;> simp only [quotient,highWord,addCarry,Bool.toNat_false,Bool.toNat_true] <;> bv_omega

def correction (q : Word) : W4 :=
  let v:=q <<< 32
  let c:=carryOut 0 (~~~v) true
  (q,addCarry 0 (~~~v) true,addCarry 0 (~~~(0:Word)) c,
    addCarry v (~~~q) (carryOut 0 (~~~(0:Word)) c))

theorem correction_value (q : Word) (hq : q.toNat≤4) :
    value (correction q)=q.toNat*(radix-p) := by
  have hq' : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 := by bv_omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

def addBack (a : W4) (c : Bool) : W4 :=
  (addWords a (if c then (0,0,0,0) else Weak.modulusWords)).1

theorem addBack_value (a : W4) (c : Bool) {n : Int}
    (hn0 : -(p:Int)≤n) (hn1 : n<21*(p:Int))
    (he : (value a:Int)+(radix:Int)*(c.toNat:Int)-radix=
      n-(n/(radix:Int)+1)*(p:Int)) :
    (value (addBack a c):Int)=n%(p:Int) := by
  have h := addWords_value a (if c then (0,0,0,0) else Weak.modulusWords)
  have hl := value_lt (addBack a c)
  have hc := Bool.toNat_le (addWords a (if c then (0,0,0,0) else Weak.modulusWords)).2
  obtain ⟨_,_,hd0,hd1⟩ := quotient_bounds n hn0 hn1
  have hm := corrected_mod n hn0 hn1
  cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true,
    Int.ofNat_zero,Int.ofNat_one,Int.mul_zero,Int.mul_one,Int.add_zero] at *
  · change value (addBack a false)+radix*(addWords a Weak.modulusWords).2.toNat=value a+p at h
    have ha := value_lt a
    rw [ite_eq_left (show n-(n/(radix:Int)+1)*(p:Int)<0 by
      simp only [radix,Weak.R] at he ha ⊢; omega)] at hm
    simp only [p,radix,Weak.R,VG.Spec.P256.p] at *
    omega
  · change value (addBack a true)+radix*(addWords a (0,0,0,0)).2.toNat=value a+0 at h
    rw [ite_eq_right (show ¬n-(n/(radix:Int)+1)*(p:Int)<0 by omega)] at hm
    have ha := value_lt a
    simp only [p,radix,Weak.R,VG.Spec.P256.p] at *
    omega
end VG.Proof.P256.Linear.FortyOne
