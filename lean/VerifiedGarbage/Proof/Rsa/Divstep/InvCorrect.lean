module
public import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrectDef

public import VerifiedGarbage.Proof.Divstep.Alg32
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

/-! # Correcting the sign and the two-bit-per-batch coefficient scale -/

@[expose] public section
namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep


 theorem corrected_range {p : Int} (st : W32.IState) (B : Nat) (hp : 0<p) :
    0≤corrected p st B ∧ corrected p st B<p :=
  ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hp⟩

 theorem corrected_cong {p x : Int} {st : W32.IState} {B : Nat}
    (h : st.inv p x (2^(2*B))) : x*corrected p st B≡|st.f| [ZMOD p] := by
  have scale : corrected p st B≡(if st.f<0 then -st.a else st.a)*2^(2*B) [ZMOD p] :=
    Int.mod_modEq _ _
  have hm := scale.mul_left x
  by_cases sign : st.f<0
  · rw [ite_eq_left sign] at hm
    have v : x*((-st.a)*2^(2*B))=-(x*st.a*2^(2*B)) := by ring
    rw [v] at hm
    rw [abs_of_neg sign]
    exact hm.trans h.1.neg.symm
  · rw [ite_eq_right sign] at hm
    rw [abs_of_nonneg (by omega)]
    exact hm.trans (by simpa only [mul_assoc] using h.1.symm)

 theorem oddInput_cong (p x : Nat) : (oddInput p x : Int)≡x [ZMOD (p : Int)] := by
  unfold oddInput
  split_ifs <;> simp [Int.ModEq,Nat.cast_add]

 theorem invRun_result {p x iv n : Nat} (odd : p%2=1) (large : 1<p)
    (inverse : (p*iv+1)%2^32=0) (pc : p<2^(32*n)) (xc : x<2^(32*n)) :
    let B := 3*(n+1)
    let st := W32.invRun 30 p iv (oddInput p x) B
    st.f.natAbs=Nat.gcd p x ∧
      (p : Int)∣(corrected p st B).toNat*(x : Int)-(Nat.gcd p x : Int) ∧
      (corrected p st B).toNat<p := by
  intro B st
  have done := invRun_done (inv:=iv) odd pc xc
  have pi : 0<(p : Int) := by exact_mod_cast (by omega : 0<p)
  have nonneg := corrected_range st B pi
  have cast : ((corrected p st B).toNat : Int)=corrected p st B := Int.toNat_of_nonneg nonneg.1
  have io : (p : Int)%2=1 := by exact_mod_cast odd
  have ii : ((p : Int)*iv+1)%2^32=0 := by exact_mod_cast inverse
  have inv := W32.invRun_inv (N:=30) (x:=(oddInput p x : Int)) (by decide) io (by exact_mod_cast large) ii B
  have hc := corrected_cong (by simpa only [show 32-30=2 from rfl] using inv)
  have cx := (oddInput_cong p x).mul_right (corrected p st B)
  have value : |st.f|=(Nat.gcd p x : Int) := by rw [←Int.natCast_natAbs,done.2]
  have result := cx.symm.trans hc
  rw [value] at result
  refine ⟨done.2,?_,?_⟩
  · rw [cast,mul_comm]
    exact result.symm.dvd
  · have hnat : (0 : Int)≤corrected p st B := nonneg.1
    exact_mod_cast (by rw [cast]; exact nonneg.2 : ((corrected p st B).toNat : Int)<p)

end VG.Proof.Rsa.Divstep
