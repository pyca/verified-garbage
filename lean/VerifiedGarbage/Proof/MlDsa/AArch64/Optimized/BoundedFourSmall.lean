import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Failure masking is per lane, so every output remains a small polynomial
regardless of the aggregate four-lane return value. -/
theorem Result.small {σ t : State} {η : Nat} (h : Result σ t (sampledRows σ η))
    {i : Nat} (hi : i<4) :
    ∃x : IPoly,polyAt t.mem (outputAt (samplerOut σ) i)=toRq x ∧
      VG.Proof.MlDsa.KeyGen.Small η x := by
  by_cases hf : (sampledRows σ η i).length=256
  · have hs := rejBounded_some η
      (ρ := Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) (B := 544)
      (by simpa only [sampledRows_H] using hf)
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hs
    refine ⟨x,?_,VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    rw [h.full hi hf,sampledRows_H]
    exact he.symm
  · refine ⟨Vector.replicate 256 0,?_,VG.Proof.MlDsa.KeyGen.small_zero η⟩
    apply Vector.ext
    intro j hj
    simp only [polyAt,Vector.getElem_ofFn,h.words i hi j hj,resultWord,ite_eq_right hf,
      toRq,Vector.getElem_map,Vector.getElem_replicate]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
