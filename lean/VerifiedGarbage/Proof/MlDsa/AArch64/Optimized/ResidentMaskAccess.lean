import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbArgs

/-! ## From `ResidentMaskInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (pro zero absorb)

theorem Env.lowStep {σ s t : State} {rs : List Reg} {W : List Region} (h : Env σ s)
    (hk : RegKeep rs s t) (hf : Frame W s.mem t.mem)
    (hregs : ∀ r∈[Reg.x19,.x20,.x21,.x22,.x30],r∉rs)
    (hsub : ∀ r∈W, r.Sub ⟨σ.gpr .x4,7904⟩) : Env σ t := by
  refine h.step hk hf hregs ?_ ?_ ?_
  · intro r hr
    exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],fun x hx =>
      (Region.sub_prefix (by decide : 7904≤8192)) x (hsub r hr x hx)⟩
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7968) 144).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7968) (n := 144) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7904) 4).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7904) (n := 4) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)

theorem Env.seedBytes {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    Spec.Sha3.bytesAt s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 =
      Spec.Sha3.bytesAt σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 := by
  apply List.ext_getElem
  · rw [VG.Proof.MlKem.bytesAt_length,VG.Proof.MlKem.bytesAt_length]
  · intro i hi _
    rw [VG.Proof.MlKem.bytesAt_length] at hi
    rw [VG.Proof.MlKem.bytesAt_getElem,VG.Proof.MlKem.bytesAt_getElem,Offset.add_add]
    exact h.frame.bytes (R := ⟨σ.gpr .x0,132⟩) (i := 66*p+i) hp.seedSep (by change 132≤2^64; decide) (by change 66*p+i<132; omega)

theorem Env.seedState {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    seedState s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p))=
      seedState σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) := by
  rw [seedState_eq,seedState_eq,h.seedBytes hp hpn]

/-- Build the paired padded seed state while preserving the captured ABI and
both polynomial destination pointers. -/
theorem maskInit_ok (σ : State) (hp : Pre σ) :
    WP isa (.block (pro ++ zero ++ absorb 0)) σ fun t => Env σ t ∧
      PairAt t.mem (σ.gpr .x4) (seedState σ.mem (σ.gpr .x0)) (seedState σ.mem (σ.gpr .x0+66)) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_env σ hp) ?_
  intro a ha
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok ha.base (fun i hi => by
    rw [ha.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ (by omega) (by omega)⟩)) ?_
  intro b ⟨hb,hfb,hzb⟩
  have eb : Env σ b := ha.lowStep hb hfb (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide))
  refine WP.mono (absorb0_ok b (by rw [eb.rd,eb.wr,eb.seed]; exact hp.seed)
    (by rw [eb.wr,eb.base]; exact hp.scratch)
    (by rw [eb.seed,eb.base]
        exact (hp.seedSep ⟨σ.gpr .x4,8192⟩ (by simp [writes])).sub_right (Region.sub_prefix (by decide)))
    (by simpa only [eb.base] using hzb)) ?_
  intro t ⟨ht,hft,hpt⟩
  have hf : Frame [pairR (σ.gpr .x4)] b.mem t.mem := by simpa only [eb.base] using hft
  refine ⟨eb.lowStep ht hf (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide)),?_⟩
  rw [eb.base,eb.seed] at hpt
  have hleft : seedState b.mem (σ.gpr .x0)=seedState σ.mem (σ.gpr .x0) := by
    simpa only [Nat.mul_zero,BitVec.add_zero] using eb.seedState hp (p := 0) (by decide)
  have hright : seedState b.mem (σ.gpr .x0+66)=seedState σ.mem (σ.gpr .x0+66) :=
    eb.seedState hp (p := 1) (by decide)
  simpa only [hleft,hright] using hpt

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskSponge.lean` -/

section

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

end

/-! ## From `ResidentMaskAccess.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

theorem pairAccess_ok {σ s : State} {d : Nat} (hp : Pre σ) (he : Env σ s)
    (hd : d=18 ∨ d=20) : PairAccess d s := by
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  have hs : ∀ p∈[Reg.x21,.x22],
      (Region.mk (σ.gpr .x4) 8192).Disjoint ⟨s.gpr p,1024⟩ := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1]; exact hp.out1Sep.symm
    · rw [he.out2]; exact hp.out2Sep.symm
  have hw : ∀ p∈[Reg.x21,.x22], (Region.mk (s.gpr p) 1024)∈s.wr := by
    intro p hp'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [he.out1,he.wr]; exact hp.out1
    · rw [he.out2,he.wr]; exact hp.out2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro off hoff j hj
    rw [he.base,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · intro p hp' j hj g hg
    rw [Offset.add_add]
    exact ⟨_,hw p hp',Offset.contains_base _ (by omega) (by omega)⟩
  · intro off hoff p hp'
    rw [he.base]
    refine (hs p hp').sub_left (Offset.sub_base _ ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega
  · rw [he.out1,he.out2]; exact hp.outputs

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
