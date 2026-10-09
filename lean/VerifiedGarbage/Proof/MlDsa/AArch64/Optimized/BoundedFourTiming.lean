import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourEndTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourChunkLeak

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure SamplerPublic (η : Nat) (σ τ : State) : Prop extends SamplerBases σ τ where
 seed : samplerSeed σ=samplerSeed τ
 leak : rejBoundedFourLeak η σ.mem (samplerSeed σ)=rejBoundedFourLeak η τ.mem (samplerSeed τ)

theorem setup_relCT {η : Nat} {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup)
      (fun s t=>SamplerRun σ s (samplerA σ) (fun _=>[]) ∧
        SamplerRun τ t (samplerA τ) (fun _=>[])) := by
  obtain ⟨_,hc⟩:=samplerSetup_taint
  have ct : RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      rcases h with ⟨rfl,rfl⟩
      apply VG.Proof.MlKem.AArch64.agree_of hb.sp
      intro r hr
      rcases (show r=Reg.x0∨r=Reg.x1∨r=Reg.x2 by simpa using hr) with rfl|rfl|rfl
      · exact hb.seed
      · exact hb.output
      · exact hb.scratch) hc
  exact (ct.wp (F₁ := Ready σ) (F₂ := Ready τ) (fun _ _ h=>by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨samplerSetup_ok hp,samplerSetup_ok hq⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>⟨h.2.1.running,h.2.2.running⟩)

/-- All data-dependent parsing and retry decisions are determined by the
original scalar rejection transcript; coefficient values remain secret. -/
theorem sampler_relCT (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (fun s t=>Result σ s (sampledRows σ η) ∧ Result τ t (sampledRows τ η)) := by
  have h0 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).1
  have h1 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).2
  have hl : ∀i<4,(rbFold η [] (chunkBytes (samplerA σ i))).length=
      (rbFold η [] (chunkBytes (samplerA τ i))).length := by
    intro i hi
    exact rbFold_length_congr rfl (h0 i hi)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change RelCT isa _ (.seq (.block samplerSetup) _) _
  apply RelCT.seq (setup_relCT hp hq hb)
  apply RelCT.assoc
  apply RelCT.seq (sampleRound_relCT sha3 hη (Or.inl rfl) hp hq hb.toSamplerBases
    (fun _ _=>rfl) h0)
  apply RelCT.seq (flagsStage_relCT hp hq hb.toSamplerBases)
  change RelCT isa _ (.seq (secondBatch sha3 η) _) _
  apply RelCT.seq (secondBatch_relCT sha3 hη hp hq hb.toSamplerBases hl h1)
  change RelCT isa _ (.seq maskFour _) _
  exact RelCT.seq (maskStage_relCT hp hq hb.toSamplerBases)
    (finish_relCT hp hq hb.toSamplerBases)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
