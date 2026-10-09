import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourShake
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Spec.MlDsa.BoundedFour

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- The public transcript already determines each stream's rejection bits. -/
theorem fourLeak_stream {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    rejBoundedLeak η (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66)=
      rejBoundedLeak η (Spec.Sha3.bytesAt τ.mem (samplerSeedAt τ i) 66) := by
  exact VG.Proof.MlDsa.KeyGen.flatMap_range_inj
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _)
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _) h i hi

/-- Splitting the original SHAKE rejection transcript adds no observable data. -/
theorem fourLeak_chunks {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    (chunkBytes (samplerA σ i)).map (hbOks η)=
      (chunkBytes (samplerA τ i)).map (hbOks η) ∧
    (chunkBytes (Resident.permuted (samplerA σ i) 2)).map (hbOks η)=
      (chunkBytes (Resident.permuted (samplerA τ i) 2)).map (hbOks η) := by
  have he := leak_hbOks (fourLeak_stream h hi) (B := 544) (by decide)
  rw [←chunks_H,←chunks_H,List.map_append,List.map_append] at he
  exact List.append_inj he (by simp only [List.length_map,chunkBytes_length])

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
