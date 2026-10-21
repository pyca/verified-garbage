module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Normalize
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.DoubleLoop
public import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrectDef
import Mathlib.Data.Int.ModEq

/-! # Connecting the machine's sign and scale corrections to the inverse -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch

 theorem normal_range {p a : Nat} (f : Int) (hp : 0<p) (ha : a<p) : normal p a f<p := by
  unfold normal
  split_ifs
  · exact Nat.mod_lt _ hp
  · exact ha

 theorem normal_cast {p a : Nat} (f : Int) (ha : a<p) :
    (normal p a f : Int)=(if f<0 then -(a : Int) else (a : Int))%p := by
  unfold normal
  split_ifs with h
  · rw [Int.natCast_emod,Int.ofNat_sub (by omega)]
    exact Int.neg_emod_eq_sub_emod.symm
  · exact (Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha)).symm

 theorem correction_eq {p a n : Nat} {st : VG.Proof.Divstep.W32.IState}
    (ha : a<p) (sa : st.a=(a : Int)) :
    doubled p (normal p a st.f) (6*(n+1))=
      (VG.Proof.Rsa.Divstep.corrected p st (3*(n+1))).toNat := by
  apply Int.ofNat_inj.mp
  rw [doubled,Int.natCast_emod,Int.natCast_mul,Int.natCast_pow,normal_cast _ ha]
  unfold VG.Proof.Rsa.Divstep.corrected
  rw [sa]
  have exp : 2*(3*(n+1))=6*(n+1) := by omega
  rw [exp,Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  exact ((Int.mod_modEq _ _).mul_right _).eq

end VG.Proof.Rsa.X86.InvBatch
