import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRunState

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.Sha3.AArch64.Neon

theorem squeezeStage_ok (sha3 : Bool) {σ s : State} (hp : SamplerPre σ)
    {A : Nat→Spec.Sha3.State} {L : Nat→List Zq} (hs : SamplerRun σ s A L)
    {off : Nat} (ho : off≤272) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeezeTwo sha3 off) s fun t=>
      SamplerRun σ t (fun i=>Resident.permuted (A i) 2) L ∧
      (∀i<4,Stream136 t.mem (inputAt (samplerScratch σ) i off) 2 (A i)) := by
  refine WP.mono (squeezeTwo_ok sha3 ho hs.env.x19 hs.pair0 hs.pair1
    (fun o n h=>sampler_in_work hp hs.env.wr h)) fun t ht=>?_
  have hlow : ∀r∈(squeezeCfg (samplerScratch σ) off).writes,
      Region.Sub r ⟨samplerScratch σ,4096⟩ := fun _ hr=>squeezeWrites_sub ho hr
  have ho' : (samplerOutput σ).Disjoint (⟨samplerScratch σ,4096⟩ : Region) :=
    hp.output_work.sub_right (Region.sub_prefix (by decide))
  have htable : (⟨samplerScratch σ+6000,1024⟩ : Region).Disjoint ⟨samplerScratch σ,4096⟩ := by
    have hh := (Offset.disjoint (samplerScratch σ)
      (d := 6000) (e := 0) (n := 1024) (k := 4096) (by decide) (by decide) (by decide))
    simp only [BitVec.add_zero] at hh
    exact hh
  refine ⟨⟨?_,ht.first,ht.second,hs.table.frame ht.frame (fun r hr=>htable.sub_right (hlow r hr)),?_,⟩,?_⟩
  · exact hs.env.lowStep ht.frame (fun r hr=>fun x hx=>
      (Region.sub_prefix (by decide : 4096≤7968)) x (hlow r hr x hx))
      ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr=>ht.keep.gpr r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl <;> decide))
  · refine ⟨hs.fields.bound,?_,?_⟩
    · intro i hi
      exact stored_frame ht.frame (fun r hr=>(ho'.sub_left (outputAt_sub _ hi)).sub_right (hlow r hr))
        (hs.fields.stored i hi) (hs.fields.bound i hi)
    · intro i hi
      have hc : (⟨countAt (samplerScratch σ) i,8⟩ : Region).Disjoint ⟨samplerScratch σ,4096⟩ := by
        have hh := (Offset.disjoint (samplerScratch σ)
          (d := 7904+8*i) (e := 0) (n := 8) (k := 4096) (by omega) (by omega) (by decide))
        simp only [BitVec.add_zero] at hh
        exact hh
      rw [ht.frame.readW (Region.contains_self _ _) (fun r hr=>hc.sub_right (hlow r hr)) (by decide)]
      exact hs.fields.count i hi
  · intro i hi
    simpa only [squeezeCfg_out _ _ hi,inputAt] using ht.streams i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
