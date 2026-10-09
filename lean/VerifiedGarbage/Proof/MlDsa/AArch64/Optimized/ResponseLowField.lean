import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.Round.Decompose

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem responseDifference_poly (m : Mem) (w cs : Addr) {i : Nat} (hi : i<n) :
    responseDifference m w cs i=(sub (polyAt m w) (signedPolyAt m cs))[i]! := by
  rw [responseDifference,ofInt_sub,sub_get _ _ hi,polyAt_get _ _ hi]
  have hn (v : Nat) : ofInt (v:Int)=ofNat v := by
    apply Fin.ext
    change ((v:Int) % (q:Int)).toNat%q=v%q
    rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]
  rw [hn,getElem!_eq _ hi]
  simp only [signedPolyAt,Vector.getElem_ofFn]

theorem responseLowPass_poly (m : Mem) (w cs : Addr) (g B : Nat) :
    responseLowPass m w cs g B ↔ normRq [(sub (polyAt m w) (signedPolyAt m cs)).map
      (fun c=>ofInt (lowBits g c))]<B := by
  rw [VG.Proof.MlDsa.Round.normRq_lt]
  apply forall_congr'; intro i
  apply forall_congr'; intro hi
  rw [responseDifference_poly _ _ _ hi,
    getElem!_eq ((sub (polyAt m w) (signedPolyAt m cs)).map (fun c=>ofInt (lowBits g c))) hi,
    Vector.getElem_map,getElem!_eq _ hi]

theorem SubLowNormPost.field {g B : Nat} {m m' : Mem} {w cs low : Addr} {r : BitVec 32} {f h : Poly}
    (hp : SubLowNormPost g B m m' w cs low r) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hf : PolyIs m w f) (hh : RawPolyIs m cs h) :
    NatPolyIs m' w ((sub f h).map fun c=>(highBits g c).toNat) ∧
    SignedPolyIs m' low ((sub f h).map fun c=>ofInt (lowBits g c)) (-(g:Int)) g ∧
    r=if normRq [((sub f h).map fun c=>ofInt (lowBits g c))]<B then 1 else 0 := by
  have he (i : Nat) (hi : i<n) : responseDifference m w cs i=(sub f h)[i]! := by
    rw [responseDifference_poly _ _ _ hi,hf.2,hh.2]
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · apply Vector.ext
    intro i hi
    simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map]
    rw [hp.1 i hi,he i hi,getElem!_eq _ hi]
  · intro i hi
    rw [hp.2.1 i hi]
    exact lowBits_bounds hg _
  · intro i hi
    rw [hp.2.1 i hi,he i hi,
      getElem!_eq ((sub f h).map (fun c=>ofInt (lowBits g c))) hi,Vector.getElem_map,getElem!_eq _ hi]
  · rw [hp.2.2]
    have hiff := responseLowPass_poly m w cs g B
    rw [hf.2,hh.2] at hiff
    simp only [hiff]

end VG.Proof.MlDsa.AArch64.Optimized.Response
