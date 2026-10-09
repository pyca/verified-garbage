import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem PairedLowPost.field {g B : Nat} {m m' : Mem} {c secret out low : Addr}
    {r : BitVec 32} {f : Nat → Poly}
    (hp : PairedLowPost g B m m' c secret out low r)
    (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hf : ∀j<2,pairedDifference m c secret out j=f j) :
    (∀j<2,NatPolyIs m' (pairPolyPtr out j) ((f j).map fun x=>(highBits g x).toNat) ∧
      SignedPolyIs m' (pairPolyPtr low j) (pairedLowPoly g (f j)) (-(g:Int)) g) ∧
    r=if normRq ((List.range 2).map fun j=>pairedLowPoly g (f j))<B then 1 else 0 := by
  refine ⟨?_,?_⟩
  · intro j hj
    refine ⟨?_,⟨?_,?_⟩⟩
    · apply Vector.ext
      intro i hi
      simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map]
      rw [(hp.1 j hj i hi).1,hf j hj,getElem!_eq _ hi]
    · intro i hi
      rw [(hp.1 j hj i hi).2]
      exact Response.lowBits_bounds hg _
    · intro i hi
      rw [(hp.1 j hj i hi).2,hf j hj]
      simp only [pairedLowPoly,getElem!_eq _ hi,Vector.getElem_map]
  · rw [hp.2]
    have he : ((List.range 2).map fun j=>pairedLowPoly g (pairedDifference m c secret out j))=
        ((List.range 2).map fun j=>pairedLowPoly g (f j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hf j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
