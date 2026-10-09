import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchStage

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

def chunkBytes (A : Spec.Sha3.State) : List Byte :=
 List.ofFn fun i : Fin 272=>Proof.Sha3.byteOf (Resident.permuted A (i.val/136+1)) (i.val%136)

theorem chunkBytes_length (A : Spec.Sha3.State) : (chunkBytes A).length=272 := List.length_ofFn

theorem chunkBytes_get (A : Spec.Sha3.State) {i : Nat} (hi : i<272) :
    (chunkBytes A)[i]! =Proof.Sha3.byteOf (Resident.permuted A (i/136+1)) (i%136) := by
  simp only [chunkBytes,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]

theorem sampleRound_ok (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) {σ s : State}
    (hp : SamplerPre σ) {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off)) s fun t=>
      SamplerRun σ t (fun i=>Resident.permuted (A i) 2) (fun i=>rbFold η (L i) (chunkBytes (A i))) := by
  refine WP.seq (WP.mono (squeezeStage_ok sha3 hp hs ho) fun t ⟨ht,hstreams⟩=>?_)
  have hl : BatchLayout t (samplerScratch σ) (samplerOut σ) off (fun i=>chunkBytes (A i)) :=
    samplerBatchLayout_ok hp ht.env.wr ho (fun _ _=>chunkBytes_length _) (fun i hi j hj=>by
      rw [chunkBytes_get _ hj]
      exact stream136_byte (hstreams i hi) (by omega))
  exact batchStage_ok hη hp ht ho hl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
