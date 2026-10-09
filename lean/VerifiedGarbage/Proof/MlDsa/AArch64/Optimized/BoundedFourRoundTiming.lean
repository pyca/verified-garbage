import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRound

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (squeezeTwo batch)

structure SamplerBases (σ τ : State) : Prop where
 scratch : samplerScratch σ=samplerScratch τ
 output : samplerOut σ=samplerOut τ
 sp : σ.sp=τ.sp

theorem sampleRound_relCT (sha3 : Bool) {η off : Nat} (hη : η=2∨η=4) (ho : off=0∨off=272)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq}
    (hl : ∀i<4,(L i).length=(M i).length)
    (hx : ∀i<4,(chunkBytes (A i)).map (hbOks η)=(chunkBytes (B i)).map (hbOks η)) :
    RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off))
      (fun s t=>SamplerRun σ s (fun i=>Resident.permuted (A i) 2)
        (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        SamplerRun τ t (fun i=>Resident.permuted (B i) 2)
        (fun i=>rbFold η (M i) (chunkBytes (B i)))) := by
  obtain ⟨_,hc⟩:=squeezeTwo_taint sha3 ho
  have cs : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19)
      (squeezeTwo sha3 off) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) hc
  have ct : RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off)) (fun _ _=>True) := by
    intro s t tr ur u v h es et
    cases es with | seq es0 es1 =>
      cases et with | seq et0 et1 =>
        have e0:=(cs _ _ _ _ _ _ ⟨by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp,
          by rw [h.1.env.x19,h.2.env.x19]; exact hb.scratch⟩ es0 et0).1
        obtain ⟨_,_,ex,ha⟩:=squeezeStage_ok sha3 hp h.1 (by omega : off≤272)
        obtain ⟨_,_,ey,hd⟩:=squeezeStage_ok sha3 hq h.2 (by omega : off≤272)
        obtain ⟨_,rfl⟩:=Exec.det es0 ex
        obtain ⟨_,rfl⟩:=Exec.det et0 ey
        have lx : BatchLayout _ (samplerScratch σ) (samplerOut σ) off (fun i=>chunkBytes (A i)) :=
          samplerBatchLayout_ok hp ha.1.env.wr (by omega) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (ha.2 i hi) (by omega))
        have ly : BatchLayout _ (samplerScratch τ) (samplerOut τ) off (fun i=>chunkBytes (B i)) :=
          samplerBatchLayout_ok hq hd.1.env.wr (by omega) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (hd.2 i hi) (by omega))
        have ia : BatchInv _ _ (samplerScratch σ) (samplerOut σ) L :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,ha.1.env.x19,ha.1.env.x21,ha.1.table,ha.1.fields⟩
        have ib : BatchInv _ _ (samplerScratch τ) (samplerOut τ) M :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,hd.1.env.x19,hd.1.env.x21,hd.1.table,hd.1.fields⟩
        rw [←hb.scratch,←hb.output] at ly ib
        have e1:=(batch_relCT hη ho lx ly
          (by rw [ha.1.env.sp,hd.1.env.sp]; exact hb.sp) hl hx _ _ _ _ _ _ ⟨ia,ib⟩ es1 et1).1
        exact ⟨by rw [e0,e1],trivial⟩
  exact (ct.wp (fun _ _ h=>⟨sampleRound_ok sha3 hη hp h.1 (by omega),
      sampleRound_ok sha3 hη hq h.2 (by omega)⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
