import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round

/-- The wrapped high-bit case is precisely the large positive remainder. -/
theorem lowBits_centered {g : Nat} (hg : IsG g) (r : Zq) :
    let a : Int := (r.val:Int)-(hbF g r.val%hbM g)*(2*g)
    lowBits g r=a-(if 4190208<a then 8380417 else 0) := by
  rw [lowBits_eq (mem_of_isG hg)]
  have hr := r.isLt
  rcases hg with rfl | rfl <;>
    simp only [hbF,hbM,q,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88] at * <;> omega

theorem lowBits_bounds {g : Nat} (hg : IsG g) (r : Zq) :
    -(g:Int)≤lowBits g r ∧ lowBits g r≤(g:Int) := by
  rw [lowBits_eq (mem_of_isG hg)]
  have hr := r.isLt
  rcases hg with rfl | rfl <;>
    simp only [hbF,hbM,q,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88] at * <;> omega

/-- The first conditional addition canonicalizes a reduced signed difference. -/
theorem reduce_signCorrected {x : BitVec 32} (hl : -2*8380417<x.toInt) (hh : x.toInt<3*8380417) :
    (Inverse.signCorrected (reduceWord x)).toNat=(ofInt x.toInt).val := by
  have h := reduce32_bounds hl hh
  have hi := reduceWord_int x hl hh
  have he := Inverse.signCorrected_int (reduceWord x) (by omega) (by omega)
  have ht := BitVec.toInt_eq_toNat_cond (Inverse.signCorrected (reduceWord x))
  have hm := reduce32_mod x.toInt
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val x.toInt
  rw [hi] at he
  split at he <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
