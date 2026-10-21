module

public import VerifiedGarbage.Proof.Mont.Words32
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Int
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Low words and sign of a bounded signed GCD value -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.Proof.Mont

theorem encoding_low {m : Mem} {base : Addr} {d n : Nat} {f : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1))) :
    (val32 m base d n : Int)%2^(32*n)=f%2^(32*n) := by
  have D : (2:Int)^(32*n) ∣ 2^(32*(n+1)) := pow_dvd_pow 2 (by omega)
  have E : (val32 m base d n : Int)%2^(32*n)=(val32 m base d (n+1) : Int)%2^(32*n) := by
    rw [val32_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.add_mul_emod_self_left]
  rw [E,← Int.emod_emod_of_dvd _ D,h,Int.emod_emod_of_dvd _ D]

theorem encoding_sign {m : Mem} {base : Addr} {d n : Nat} {f : Int}
    (h : (val32 m base d (n+1) : Int)%2^(32*(n+1))=f%2^(32*(n+1))) (hb : |f|<2^(32*n)) :
    (2^31 ≤ w32 m base (d+4*n)) ↔ f<0 := by
  have grow : (2:Int)^(32*n) ≤ (2:Int)^(32*n)*2^31 := by
    have hp : (0:Int)<2^(32*n) := by positivity
    nlinarith
  have hb' := abs_lt.mp hb
  have lo : -((2:Int)^(32*n)*2^31) ≤ f := by omega
  have hi : f<(2:Int)^(32*n)*2^31 := by omega
  have Q : (2:Int)^(32*(n+1))=2*((2:Int)^(32*n)*2^31) := by
    rw [show 32*(n+1)=32*n+32 by omega,pow_add]
    ring
  have hV : (val32 m base d (n+1) : Int)<2*((2:Int)^(32*n)*2^31) := by
    rw [← Q]
    exact_mod_cast val32_lt m base d (n+1)
  rw [Q] at h
  have T := Divstep.W32.tc_eq (by positivity) lo hi (Int.natCast_nonneg _) hV h
  have sign := Divstep.W32.tc_neg lo hi T
  rw [VG.Proof.Weierstrass.X86.Inv.sign32]
  have H : ((2^(32*n)*2^31 : Nat) : Int)=(2:Int)^(32*n)*2^31 := by push_cast; rfl
  rw [← H] at sign
  exact_mod_cast sign

end VG.Proof.Rsa.X86.GcdBatch
