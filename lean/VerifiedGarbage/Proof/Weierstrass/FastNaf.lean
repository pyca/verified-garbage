import VerifiedGarbage.Proof.Weierstrass.Naf5
import VerifiedGarbage.Proof.Weierstrass.FastNaf7

/-! Shared interface for the two public verification NAF widths. -/
namespace VG.Proof.Weierstrass.FastNaf
open Spec.Weierstrass

def Width (w : Nat) : Prop := w=5 ∨ w=7

def next (w n : Nat) : Nat := if w=7 then FastNaf7.next n else Naf5.next n

def residual (w k j : Nat) : Nat := if w=7 then FastNaf7.residual k j else Naf5.residual k j

def negative (w k j : Nat) : Bool := if w=7 then FastNaf7.negative k j else Naf5.negative k j

def magnitude (w k j : Nat) : Nat := if w=7 then FastNaf7.magnitude k j else Naf5.magnitude k j

def digit (w k j : Nat) : Int := if w=7 then FastNaf7.digit k j else Naf5.digit k j

def byte (w k j : Nat) : BitVec 8 := if w=7 then FastNaf7.byte k j else Naf5.byte k j

def point (C : Curve) (P : Point C) (w k j : Nat) : Point C :=
  if negative w k j then negPt (mul (magnitude w k j) P) else mul (magnitude w k j) P

theorem residual_zero (w k : Nat) :
    residual w k 0=k := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.residual_zero k
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.residual_zero k

theorem residual_succ (w k j : Nat) :
    residual w k (j+1)=next w (residual w k j) := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.residual_succ k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.residual_succ k j

theorem magnitude_le {w : Nat} (hw : Width w) (k j : Nat) :
    magnitude w k j≤2^(w-1)-1 := by
  rcases hw with rfl | rfl
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,Nat.reduceSub,Nat.reducePow,ite_false,ite_true,show ¬(5=7) from by decide] using Naf5.magnitude_le k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,Nat.reduceSub,Nat.reducePow,ite_false,ite_true] using FastNaf7.magnitude_le k j

theorem magnitude_odd_or_zero (w k j : Nat) :
    magnitude w k j=0 ∨ magnitude w k j%2=1 := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.magnitude_odd_or_zero k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.magnitude_odd_or_zero k j

theorem magnitude_zero_iff (w k j : Nat) :
    magnitude w k j=0 ↔ residual w k j%2=0 := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.magnitude_zero_iff k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.magnitude_zero_iff k j

theorem recurrence (w k j : Nat) :
    if negative w k j then residual w k j+magnitude w k j=2*residual w k (j+1) else residual w k j=2*residual w k (j+1)+magnitude w k j := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.recurrence k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.recurrence k j

theorem negative_magnitude_pos (w k j : Nat) (h : negative w k j=true) :
    0<magnitude w k j := by
  by_cases h7 : w=7
  · have h : FastNaf7.negative k j=true := by simpa only [negative,h7,ite_true,ite_false] using h
    simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.negative_magnitude_pos k j h
  · have h : Naf5.negative k j=true := by simpa only [negative,h7,ite_true,ite_false] using h
    simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.negative_magnitude_pos k j h

theorem byte_toNat (w k j : Nat) :
    (byte w k j).toNat=if negative w k j then 256-magnitude w k j else magnitude w k j := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.byte_toNat k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.byte_toNat k j

theorem byte_magnitude (w k j : Nat) :
    (if (byte w k j).toNat<128 then (byte w k j).toNat else 256-(byte w k j).toNat)=magnitude w k j := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.byte_magnitude k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.byte_magnitude k j

theorem byte_negative (w k j : Nat) :
    decide (128≤(byte w k j).toNat)=negative w k j := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.byte_negative k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.byte_negative k j

theorem byte_zero_iff (w k j : Nat) :
    byte w k j=0 ↔ magnitude w k j=0 := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.byte_zero_iff k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.byte_zero_iff k j

theorem residual_bound (w : Nat) {k : Nat} (hk : k≤2^256) {j : Nat} (hj : j≤256) :
    residual w k j≤2^(256-j) := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.residual_bound hk hj
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.residual_bound hk hj

theorem residual_zero257 (w : Nat) {k : Nat} (hk : k<2^256) :
    residual w k 257=0 := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.residual_zero257 hk
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.residual_zero257 hk

theorem add_step {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true) (w k j : Nat) :
    Spec.Weierstrass.add (mul (2*residual w k (j+1)) P) (point C P w k j)=mul (residual w k j) P := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.add_step hC hP k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.add_step hC hP k j

theorem onCurve_point {C : Curve} (hC : Law C) {P : Point C} (hP : onCurve C P=true) (w k j : Nat) :
    onCurve C (point C P w k j)=true := by
  by_cases h7 : w=7
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using FastNaf7.onCurve_point hC hP k j
  · simpa only [next,residual,negative,magnitude,digit,byte,point,FastNaf7.point,Naf5.point,h7,ite_true,ite_false] using Naf5.onCurve_point hC hP k j


theorem next_even (w n : Nat) (hn : n%2=0) : next w n=n/2 := by
  simp only [next,Naf5.next,FastNaf7.next,hn,ite_true]
  split <;> rfl

theorem next_double (w n : Nat) : next w (2*n)=n := by
  rw [next_even w _ (by omega)]
  omega

theorem residual_add (w k j i : Nat) : residual w k (j+i)=residual w (residual w k j) i := by
  induction i with
  | zero => simp only [Nat.add_zero,residual_zero]
  | succ i ih => rw [Nat.add_succ,residual_succ,ih,residual_succ]

theorem residual_pow (w n e i : Nat) (hi : i≤e) :
    residual w (2^e*n) i=2^(e-i)*n := by
  induction e generalizing i with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    rw [residual_zero]
  | succ e ih =>
    cases i with
    | zero => rw [residual_zero,Nat.sub_zero]
    | succ i =>
      rw [show i+1=1+i from by omega,residual_add,residual_succ,residual_zero,
        Nat.pow_succ,show 2^e*2*n=2*(2^e*n) from by simp only [Nat.mul_assoc,Nat.mul_left_comm],next_double,
        ih i (by omega),show e+1-(1+i)=e-i from by omega]

theorem next_odd {w : Nat} (hw : Width w) (n : Nat) (hn : n%2≠0) :
    next w n=2^(w-1)*((n+2^(w-1))/2^w) := by
  rcases hw with rfl | rfl <;>
    simp only [next,Naf5.next,FastNaf7.next,Nat.reduceSub,Nat.reducePow,
      show ¬(5=7) from by decide,ite_false,ite_true,hn,Nat.mul_comm]

theorem residual_skip {w : Nat} (hw : Width w) (k j : Nat)
    (hn : residual w k j%2≠0) :
    residual w k (j+w)=(residual w k j+2^(w-1))/2^w := by
  have hw0 : 0<w := by rcases hw with rfl | rfl <;> decide
  rw [show j+w=j+1+(w-1) from by omega,residual_add,residual_succ,next_odd hw _ hn,
    residual_pow w _ (w-1) (w-1) (by omega),Nat.sub_self,Nat.pow_zero,Nat.one_mul]

theorem residual_skip_between {w : Nat} (hw : Width w) (k j i : Nat)
    (hn : residual w k j%2≠0) (hi : 0<i) (hiw : i≤w) :
    residual w k (j+i)=2^(w-i)*((residual w k j+2^(w-1))/2^w) := by
  rw [show j+i=j+1+(i-1) from by omega,residual_add,residual_succ,next_odd hw _ hn,
    residual_pow w _ (w-1) (i-1) (by omega),show w-1-(i-1)=w-i from by omega]

theorem byte_skip_zero {w : Nat} (hw : Width w) (k j i : Nat)
    (hn : residual w k j%2≠0) (hi : 0<i) (hiw : i<w) : byte w k (j+i)=0 := by
  rw [byte_zero_iff,magnitude_zero_iff,residual_skip_between hw k j i hn hi (by omega)]
  have he : w-i=(w-i-1)+1 := by omega
  rw [he,Nat.pow_succ]
  simp only [Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mul,Nat.zero_mod]

theorem residual_of_zero (w k j : Nat) (hz : residual w k j=0) (i : Nat) :
    residual w k (j+i)=0 := by
  induction i with
  | zero => simpa only [Nat.add_zero] using hz
  | succ i ih => rw [Nat.add_succ,residual_succ,ih,next_even w 0 (by decide)]

theorem byte_of_zero (w k j : Nat) (hz : residual w k j=0) : byte w k j=0 := by
  rw [byte_zero_iff,magnitude_zero_iff,hz]

theorem residual_zero_ge {w k j : Nat} (hk : k<2^256) (hj : 257≤j) :
    residual w k j=0 := by
  rw [show j=257+(j-257) from by omega]
  exact residual_of_zero w k 257 (residual_zero257 w hk) _

end VG.Proof.Weierstrass.FastNaf
