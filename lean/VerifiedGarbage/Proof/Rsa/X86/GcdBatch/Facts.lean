module
import Mathlib.Algebra.Order.Ring.Abs

public import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Loop
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Tc32
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Divstep.Steps
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith

/-! # Arithmetic bounds for all RSA GCD batches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG.Proof.Divstep

theorem runFacts {n m x p i : Nat} (hn : n ≤ 1024) (hi : i<3*(n+1))
    (hm : m%2=1) (mp : m≤p) (xp : x≤p) :
    Facts (divsteps (30*i) (1,m,x)) p := by
  have d := W32.divsteps_d (1,m,x) (30*i)
  have ho := divsteps_odd (d:=1) (f:=m) (g:=x) (by decide) (by exact_mod_cast hm) (30*i)
  have fg := W32.divsteps_le (M:=p) (d:=1) (f:=m) (g:=x) (by decide) (by exact_mod_cast hm)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (m:Int)≤p by exact_mod_cast mp))
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (x:Int)≤p by exact_mod_cast xp)) (30*i)
  refine ⟨?_,ho.2,fg.1,fg.2⟩
  norm_num only [abs_one,Nat.cast_mul,Nat.cast_ofNat] at d
  omega

theorem initial_bound {n m x : Nat} (hm : m<2^(32*n)) (hx : x<2^(32*n)) :
    max m (VG.Proof.Rsa.Divstep.oddInput m x)<2^(32*n+1) := by
  have h := VG.Proof.Rsa.Divstep.oddInput_lt hm hx
  have pos := Nat.two_pow_pos (32*n)
  rw [Nat.pow_succ]
  omega

end VG.Proof.Rsa.X86.GcdBatch
