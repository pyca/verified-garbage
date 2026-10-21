module

public import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Divstep.Tc32
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

/-! # Batched inversion bounds for an unreduced, odd-adjusted RSA operand -/

@[expose] public section
namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

 theorem invRun_bounds {p x inv cap : Nat}
    (odd : p%2=1) (large : 1<p) (ip : (p*inv+1)%2^32=0)
    (pc : p≤cap) (xc : oddInput p x≤cap) (batches : Nat) :
    let st := W32.invRun 30 p inv (oddInput p x) batches
    |st.d|≤1+2*(30*batches : Nat) ∧ st.f%2=1 ∧ |st.f|≤cap ∧ |st.g|≤cap ∧
    0≤st.a ∧ st.a<p ∧ 0≤st.b ∧ st.b<p := by
  intro st
  have oddI : (p : Int)%2=1 := by exact_mod_cast odd
  have ipI : ((p : Int)*inv+1)%2^32=0 := by exact_mod_cast ip
  have coeff := W32.invRun_inv (N:=30) (x:=(oddInput p x : Int)) (by decide) oddI (by exact_mod_cast large) ipI batches
  have dfg := (W32.invRun_dfg (N:=30) (m:=(inv : Int)) (x:=(oddInput p x : Int)) oddI batches).1
  have df : st.f=(divsteps (30*batches) (1,p,oddInput p x)).2.1 := by rw [←dfg]
  have dg : st.g=(divsteps (30*batches) (1,p,oddInput p x)).2.2 := by rw [←dfg]
  have dd : st.d=(divsteps (30*batches) (1,p,oddInput p x)).1 := by rw [←dfg]
  have pair := W32.divsteps_le (M:=(cap : Int)) (d:=1) (f:=(p : Int)) (g:=(oddInput p x : Int))
    (by decide) oddI (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast pc)
    (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast xc) (30*batches)
  have delta := W32.divsteps_d (1,(p : Int),(oddInput p x : Int)) (30*batches)
  refine ⟨?_,(W32.invRun_dfg (N:=30) (m:=(inv : Int)) (x:=(oddInput p x : Int)) oddI batches).2,
    by rw [df]; exact pair.1,by rw [dg]; exact pair.2,coeff.2.2⟩
  rw [dd]
  simpa using delta

 theorem invRun_done {p x n inv : Nat} (odd : p%2=1)
    (pc : p<2^(32*n)) (xc : x<2^(32*n)) :
    let st := W32.invRun 30 p inv (oddInput p x) (3*(n+1))
    st.g=0 ∧ st.f.natAbs=Nat.gcd p x := by
  intro st
  have oddI : (p : Int)%2=1 := by exact_mod_cast odd
  have e := (W32.invRun_dfg (N:=30) (m:=(inv : Int)) (x:=(oddInput p x : Int)) oddI (3*(n+1))).1
  have result := oddInput_done odd pc xc
  change (divsteps (30*(3*(n+1))) (1,p,oddInput p x)).2.2=0 ∧
    (divsteps (30*(3*(n+1))) (1,p,oddInput p x)).2.1.natAbs=Nat.gcd p x at result
  rw [←e] at result
  exact result

end VG.Proof.Rsa.Divstep
