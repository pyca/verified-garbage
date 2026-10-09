import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSamplerState

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample

theorem sampler_work_read {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions (s.rd++s.wr) (samplerAt σ d) n := by
  obtain ⟨r,hr,hc⟩:=sampler_in_work hp hw hd
  exact ⟨r,List.mem_append_right _ hr,hc⟩

theorem inputAt_sub (b : Addr) {i off : Nat} (hi : i<4) (ho : off≤272) :
    Region.Sub (⟨inputAt b i off,274⟩ : Region) ⟨b,8192⟩ :=
  Offset.sub_base b (d := 840+544*i+off) (n := 274) (k := 8192) (by omega)

theorem samplerBatchLayout_ok {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {off : Nat} (ho : off≤272) {X : Nat→List Byte}
    (hlen : ∀i<4,(X i).length=272)
    (hbytes : ∀i<4,∀j<272,s.mem (inputAt (samplerScratch σ) i off+BitVec.ofNat 64 j)=(X i)[j]!) :
    BatchLayout s (samplerScratch σ) (samplerOut σ) off X := by
  let b:=samplerScratch σ
  let p:=samplerOut σ
  have hstream (i : Nat) (hi : i<4) :
      (⟨inputAt b i off,(X i).length+2⟩ : Region).Disjoint (polyR (outputAt p i)) := by
    rw [hlen i hi]
    exact (hp.output_work.symm.sub_left (inputAt_sub _ hi ho)).sub_right (outputAt_sub _ hi)
  have htable (i : Nat) (hi : i<4) :
      (⟨b+6000,1024⟩ : Region).Disjoint (polyR (outputAt p i)) :=
    (hp.output_work.symm.sub_left (Offset.sub_base b (d := 6000) (n := 1024) (k := 8192)
      (by decide))).sub_right (outputAt_sub _ hi)
  have hout (i : Nat) (hi : i<4) (j n : Nat) (hj : 4*j+n≤1024) :
      InRegions s.wr (coeffAddr (outputAt p i) j) n := by
    rw [hw,hp.wr]
    refine ⟨samplerOutput σ,by simp,?_⟩
    change Region.Contains ⟨p,4096⟩ ((p+BitVec.ofNat 64 (1024*i))+BitVec.ofNat 64 (4*j)) n
    rw [Offset.add_add]
    exact Offset.contains_base p (by omega) (by omega)
  constructor
  · exact hlen
  · intro i hi
    refine ⟨by rw [hlen i hi],by rw [hlen i hi],?_,hstream i hi,htable i hi,?_,?_,?_⟩
    · intro j hj; exact hbytes i hi j (by simpa only [hlen i hi] using hj)
    · intro d hd
      rw [hlen i hi] at hd
      change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 (840+544*i+off))+BitVec.ofNat 64 d) 4
      rw [Offset.add_add]
      exact sampler_work_read hp hw (by omega)
    · intro m hm
      constructor
      · change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*m)) 16
        rw [Offset.add_add]
        exact sampler_work_read hp hw (by omega)
      · change InRegions (s.rd++s.wr) (((b+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*m))+BitVec.ofNat 64 32) 8
        rw [Offset.add_add,Offset.add_add]
        exact sampler_work_read hp hw (by omega)
    · intro j hj; exact hout i hi j 16 (by omega)
  · intro i hi
    refine ⟨by rw [hlen i hi],?_,?_,?_,?_⟩
    · intro j hj; exact hbytes i hi j (by simpa only [hlen i hi] using hj)
    · exact (hstream i hi).sub_left (Region.sub_prefix (by omega))
    · intro d hd
      rw [hlen i hi] at hd
      change InRegions (s.rd++s.wr) ((b+BitVec.ofNat 64 (840+544*i+off))+BitVec.ofNat 64 d) 1
      rw [Offset.add_add]
      exact sampler_work_read hp hw (by omega)
    · intro j hj; exact hout i hi j 4 (by omega)
  · intro i hi r hr
    rw [hlen i hi]
    rcases (show r=⟨p,4096⟩∨r=⟨b+7904#64,32⟩ by simpa [batchWrites] using hr) with rfl|rfl
    · exact hp.output_work.symm.sub_left (inputAt_sub _ hi ho)
    · exact Offset.disjoint b (d := 840+544*i+off) (e := 7904) (n := 274) (k := 32)
        (by omega) (by omega) (by decide)
  · intro r hr
    rcases (show r=⟨p,4096⟩∨r=⟨b+7904#64,32⟩ by simpa [batchWrites] using hr) with rfl|rfl
    · exact hp.output_work.symm.sub_left (Offset.sub_base b (d := 6000) (n := 1024) (k := 8192) (by decide))
    · exact Offset.disjoint b (d := 6000) (e := 7904) (n := 1024) (k := 32) (by decide) (by decide) (by decide)
  · intro i hi j hj
    exact (hp.output_work.sub_left (outputAt_sub _ hi)).sub_right
      (Offset.sub_base b (d := 7904+8*j) (n := 8) (k := 8192) (by omega))
  · intro i hi; exact sampler_work_read hp hw (by omega)
  · intro i hi; exact sampler_in_work hp hw (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
