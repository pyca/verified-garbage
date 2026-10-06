import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Chain

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64

private theorem digit_bound {R Q A V : Nat} (ha : A<R) (hv : V<Q) : A+R*V<R*Q := by
  have h : R*V ≤ R*(Q-1) := Nat.mul_le_mul_left R (by omega)
  have e : R+R*(Q-1)=R*Q := by
    calc
      _ = R*1+R*(Q-1) := by rw [Nat.mul_one]
      _ = R*(1+(Q-1)) := (Nat.mul_add ..).symm
      _ = R*Q := by rw [show 1+(Q-1)=Q by omega]
  omega

theorem value_lt (s : State) (rs : List Reg) : value s rs<2^(64*rs.length) := by
  induction rs with
  | nil => simp only [value,List.length_nil,Nat.mul_zero,Nat.pow_zero]; decide
  | cons r rs ih =>
    rw [value,List.length_cons,show 64*(rs.length+1)=64+64*rs.length by omega,Nat.pow_add]
    exact digit_bound (s.gpr r).isLt ih

theorem value_append (s : State) (rs tail : List Reg) :
    value s (rs++tail)=value s rs+2^(64*rs.length)*value s tail := by
  induction rs with
  | nil => simp only [List.nil_append,value,List.length_nil,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  | cons r rs ih =>
    simp only [List.cons_append,value,List.length_cons,ih]
    rw [show 64*(rs.length+1)=64+64*rs.length by omega,Nat.pow_add]
    rw [Nat.mul_add,Nat.add_assoc,Nat.mul_assoc]

theorem value_zero_top {s : State} {rs : List Reg} {top : Reg} (hz : s.gpr top=0) :
    value s (rs++[top])<2^(64*((rs++[top]).length-1)) := by
  rw [value_append]
  simp only [value,hz,show (0 : BitVec 64).toNat=0 from rfl,Nat.mul_zero,Nat.add_zero,
    List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_sub_cancel]
  exact value_lt s rs

end VG.Proof.Bignum.X86_64.AdxTri8
