import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskInit

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_mov wp_addImm)

def SpongePost (σ t : State) : Prop := Env σ t ∧
  Resident.StreamOutput t.mem (σ.gpr .x4+840) 8 5 (seedState σ.mem (σ.gpr .x0)) ∧
  Resident.StreamOutput t.mem (σ.gpr .x4+1520) 8 5 (seedState σ.mem (σ.gpr .x0+66))

theorem spongeArgs_ok (s : State) :
    WP isa (.block [Impl.MlKem.AArch64.mov .x23 .x19,.addImm .x .x24 .x19 840,
      .addImm .x .x25 .x19 1520]) s fun t => Only [.x23,.x24,.x25] s t ∧
      t.gpr .x23=s.gpr .x19 ∧ t.gpr .x24=s.gpr .x19+840 ∧ t.gpr .x25=s.gpr .x19+1520 := by
  refine wp_mov fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((ha.trans hb).trans ht).mono (by simp)
  · rw [ht.get .x23,hb.get .x23,ea]
  · rw [ht.get .x24,eb,ha.get .x19]; rfl
  · rw [et,hb.get .x19,ha.get .x19]; rfl

/-- Five resident permutations and vector squeezes, retaining all outer
sampler state and its saved ABI record. -/
theorem sponge_ok (core : Resident.Core) {σ s : State} (hp : Pre σ) (he : Env σ s)
    (hpair : PairAt s.mem (σ.gpr .x4) (seedState σ.mem (σ.gpr .x0)) (seedState σ.mem (σ.gpr .x0+66)))
    (h23 : s.gpr .x23=σ.gpr .x4) (h24 : s.gpr .x24=σ.gpr .x4+840)
    (h25 : s.gpr .x25=σ.gpr .x4+1520) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith core.code .x23 .x24 .x25) s (SpongePost σ) := by
  have hw (off len : Nat) (hb : off+len≤8192) :
      InRegions s.wr (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hp0 : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 840) 680).Disjoint (pairR (σ.gpr .x4)) := by
    have hh := Offset.disjoint (σ.gpr .x4) (d := 840) (n := 680) (e := 0) (k := 400)
      (Or.inr (by decide)) (by decide) (by decide)
    simpa only [BitVec.add_zero,pairR] using hh
  have hp1 : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 1520) 680).Disjoint (pairR (σ.gpr .x4)) := by
    have hh := Offset.disjoint (σ.gpr .x4) (d := 1520) (n := 680) (e := 0) (k := 400)
      (Or.inr (by decide)) (by decide) (by decide)
    simpa only [BitVec.add_zero,pairR] using hh
  refine WP.mono (Resident.maskPairWith_ok core hpair h23 h24 h25
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) hp0 hp1
    (fun i hi => hr (16*i) 16 (by omega)) (fun i hi => hw (16*i) 16 (by omega))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega))) ?_
  intro t ht
  have hk : RegKeep [.x6,.x7,.x16,.x24,.x25,.x28] s t := by
    refine ⟨?_,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.2.2.2.2.1 r hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2 hr.1 hr.2.1 hr.2.2.1
  refine ⟨he.lowStep hk ht.2.2.2.1 (by decide) ?_,ht.2.1,ht.2.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base _ (by decide)
  · exact Offset.sub_base _ (by decide)
  · exact Region.sub_prefix (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
