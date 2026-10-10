import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSaved
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParsePair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes

/-! ## From `ResidentZero.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (zero)

theorem zeros_ok {s : State} {p : Addr} (hp : s.gpr .x19 = p)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block zero) s fun t => RegKeep [] s t ∧
      Frame [pairR p] s.mem t.mem ∧ ∀ i < 25, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zero
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [pairR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 25 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega)
    (by rw [ht.gpr .x19 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentProArgs.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_strw wp_mov)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (proArgs)

theorem proArgs_ok (s : State) (hw : InRegions s.wr (s.gpr .x4+7904) 4) :
    WP isa (.block proArgs) s fun t => RegKeep [.x19,.x20,.x21,.x22] s t ∧
      t.mem=s.mem.writeW (s.gpr .x4+7904) ((s.gpr .x1).setWidth 32) ∧
      t.gpr .x19=s.gpr .x4 ∧ t.gpr .x20=s.gpr .x0 ∧
      t.gpr .x21=s.gpr .x2 ∧ t.gpr .x22=s.gpr .x3 := by
  unfold proArgs
  refine wp_strw ⟨by decide,by decide⟩ rfl hw fun a ha => ?_
  refine wp_mov fun b hb eb => wp_mov fun c hc ec => wp_mov fun f hf ef =>
    wp_mov fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_,?_,?_⟩
  · have h0 : RegKeep [] s a := ⟨fun r _ => congrFun ha.gpr r,ha.rd,ha.wr,ha.sp⟩
    exact (h0.trans (RegKeep.only (((hb.trans hc).trans hf).trans ht))).mono (by simp)
  · rw [ht.mem,hf.mem,hc.mem,hb.mem,ha.mem]
    rfl
  · rw [ht.get .x19,hf.get .x19,hc.get .x19,eb,ha.gpr]
  · rw [ht.get .x20,hf.get .x20,ec,hb.get .x0,ha.gpr]
  · rw [ht.get .x21,ef,hc.get .x2,hb.get .x2,ha.gpr]
  · rw [et,hf.get .x3,hc.get .x3,hb.get .x3,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentPro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (pro)

structure ProPost (s t : State) : Prop where
  keep : RegKeep [.x8,.x19,.x20,.x21,.x22] s t
  saved : Saved s (s.gpr .x4) t.mem
  frame : Frame [⟨s.gpr .x4+7968,144⟩,⟨s.gpr .x4+7904,4⟩] s.mem t.mem
  base : t.gpr .x19=s.gpr .x4
  seed : t.gpr .x20=s.gpr .x0
  out1 : t.gpr .x21=s.gpr .x2
  out2 : t.gpr .x22=s.gpr .x3
  gamma : t.mem.readW (s.gpr .x4+7904) 32=(s.gpr .x1).setWidth 32

/-- Establish the resident sampler frame and retain both independent output
pointers while saving the ordinary caller ABI in the scratch tail. -/
theorem pro_ok (s : State) (hw : (Region.mk (s.gpr .x4) 8192)∈s.wr) :
    WP isa (.block pro) s (ProPost s) := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)) ?_
  intro a ⟨ha,has,haf⟩
  have a4 := ha.gpr .x4 (by decide)
  have a1 := ha.gpr .x1 (by decide)
  refine WP.mono (proArgs_ok a (by
    rw [ha.wr,a4]
    exact ⟨_,hw,Offset.contains_base _ (by decide) (by decide)⟩)) ?_
  intro t ⟨ht,hm,hbase,hseed,ho1,ho2⟩
  rw [a4,a1] at hm
  have hgamma : Frame [⟨s.gpr .x4+7904,4⟩] a.mem t.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨(ha.trans ht).mono (by simp),?_,?_,hbase.trans a4,
    hseed.trans (ha.gpr .x0 (by decide)),ho1.trans (ha.gpr .x2 (by decide)),
    ho2.trans (ha.gpr .x3 (by decide)),?_⟩
  · exact has.keep hgamma (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))
  · exact (haf.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (hgamma.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
  · rw [hm,Mem.readW_writeW_self32]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskEnv.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def writes (σ : State) : List Region :=
  [⟨σ.gpr .x4,8192⟩,⟨σ.gpr .x2,1024⟩,⟨σ.gpr .x3,1024⟩]

structure Pre (σ : State) : Prop where
  scratch : (Region.mk (σ.gpr .x4) 8192)∈σ.wr
  out1 : (Region.mk (σ.gpr .x2) 1024)∈σ.wr
  out2 : (Region.mk (σ.gpr .x3) 1024)∈σ.wr
  seed : (Region.mk (σ.gpr .x0) 132)∈σ.rd++σ.wr
  seedSep : ∀ r∈writes σ, (Region.mk (σ.gpr .x0) 132).Disjoint r
  out1Sep : (Region.mk (σ.gpr .x2) 1024).Disjoint ⟨σ.gpr .x4,8192⟩
  out2Sep : (Region.mk (σ.gpr .x3) 1024).Disjoint ⟨σ.gpr .x4,8192⟩
  outputs : (Region.mk (σ.gpr .x2) 1024).Disjoint ⟨σ.gpr .x3,1024⟩
  gamma : (σ.gpr .x1).setWidth 32=131072#32 ∨ (σ.gpr .x1).setWidth 32=524288#32

structure Env (σ s : State) : Prop where
  base : s.gpr .x19=σ.gpr .x4
  seed : s.gpr .x20=σ.gpr .x0
  out1 : s.gpr .x21=σ.gpr .x2
  out2 : s.gpr .x22=σ.gpr .x3
  lr : s.gpr .x30=σ.gpr .x30
  sp : s.sp=σ.sp
  rd : s.rd=σ.rd
  wr : s.wr=σ.wr
  saved : Saved σ (σ.gpr .x4) s.mem
  gamma : s.mem.readW (σ.gpr .x4+7904) 32=(σ.gpr .x1).setWidth 32
  frame : Frame (writes σ) σ.mem s.mem

theorem Env.step {σ s t : State} {rs : List Reg} {W : List Region} (h : Env σ s)
    (hk : RegKeep rs s t) (hf : Frame W s.mem t.mem)
    (hregs : ∀ r∈[Reg.x19,.x20,.x21,.x22,.x30],r∉rs)
    (hsub : ∀ r∈W, ∃ r'∈writes σ, r.Sub r')
    (hsave : ∀ r∈W, (Region.mk (σ.gpr .x4+7968) 144).Disjoint r)
    (hgamma : ∀ r∈W, (Region.mk (σ.gpr .x4+7904) 4).Disjoint r) : Env σ t := by
  refine ⟨(hk.gpr _ (hregs _ (by simp))).trans h.base,
    (hk.gpr _ (hregs _ (by simp))).trans h.seed,
    (hk.gpr _ (hregs _ (by simp))).trans h.out1,
    (hk.gpr _ (hregs _ (by simp))).trans h.out2,
    (hk.gpr _ (hregs _ (by simp))).trans h.lr,
    hk.sp.trans h.sp,hk.rd.trans h.rd,hk.wr.trans h.wr,h.saved.keep hf hsave,?_,h.frame.trans (hf.sub hsub)⟩
  rw [hf.readW (Region.contains_self _ _) hgamma (by decide)]
  exact h.gamma

theorem pro_env (σ : State) (hp : Pre σ) : WP isa (.block Impl.MlDsa.AArch64.Optimized.ResidentMask.pro) σ (Env σ) := by
  refine WP.mono (pro_ok σ hp.scratch) ?_
  intro s h
  refine ⟨h.base,h.seed,h.out1,h.out2,h.keep.gpr .x30 (by decide),h.keep.sp,
    h.keep.rd,h.keep.wr,h.saved,h.gamma,h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],Offset.sub_base _ (by decide)⟩
  · exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],Offset.sub_base _ (by decide)⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentAbsorbArgs.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_addImm)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (absorb)

private theorem args_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x19 0,.addImm .x .x3 .x20 0,.addImm .x .x4 .x3 66]) s
      fun t => Only [.x2,.x3,.x4] s t ∧ t.gpr .x2=s.gpr .x19 ∧
        t.gpr .x3=s.gpr .x20 ∧ t.gpr .x4=s.gpr .x20+66 := by
  refine wp_addImm (by decide) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_addImm (by decide) fun t ht et => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((ha.trans hb).trans ht).mono (by simp)
  · rw [ht.get .x2,hb.get .x2,ea]; exact BitVec.add_zero _
  · rw [ht.get .x3,eb,ha.get .x20]; exact BitVec.add_zero _
  · rw [et,eb,ha.get .x20,BitVec.add_zero]; rfl

/-- Absorb the two independent 66-byte seeds into the single paired state. -/
theorem absorb0_ok (s : State)
    (hin : (Region.mk (s.gpr .x20) 132)∈s.rd++s.wr)
    (hw : (Region.mk (s.gpr .x19) 8192)∈s.wr)
    (hsep : (Region.mk (s.gpr .x20) 132).Disjoint ⟨s.gpr .x19,400⟩)
    (hz : ∀ i<25, s.mem.read (wordAddr (s.gpr .x19) i) 16=0) :
    WP isa (.block (absorb 0)) s fun t => RegKeep [.x2,.x3,.x4,.x6,.x7,.x8,.x9] s t ∧
      Frame [pairR (s.gpr .x19)] s.mem t.mem ∧
      PairAt t.mem (s.gpr .x19) (seedState s.mem (s.gpr .x20)) (seedState s.mem (s.gpr .x20+66)) := by
  unfold absorb
  simp only [Nat.mul_zero]
  rw [WP.block_append_iff]
  refine WP.mono (args_ok s) ?_
  intro a ⟨ha,h2,h3,h4⟩
  have input (off len : Nat) (hb : off+len≤132) :
      InRegions (a.rd++a.wr) (s.gpr .x20+BitVec.ofNat 64 off) len := by
    rw [ha.rd,ha.wr]
    exact ⟨_,hin,Offset.contains_base _ hb (by omega)⟩
  refine WP.mono (absorbBody_ok h2 h3 h4
    (fun j hj => input (8*j) 8 (by omega))
    (fun j hj => by
      change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 (8*j)) 8
      rw [Offset.add_add]; exact input (66+8*j) 8 (by omega))
    (input 64 1 (by decide)) (input 65 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 64) 1
        rw [Offset.add_add]; exact input (66+64) 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 65) 1
        rw [Offset.add_add]; exact input (66+65) 1 (by decide))
    (fun j hj => by rw [ha.wr]; exact ⟨_,hw,Offset.contains_base _ (by omega) (by omega)⟩)
    (hsep.sub_left (Region.sub_prefix (by decide)))
    (hsep.sub_left (Offset.sub_base _ (by decide)))
    (by simpa only [ha.mem] using hz)) ?_
  intro t ⟨ht,hf,hpair⟩
  refine ⟨((RegKeep.only ha).trans ht).mono (by simp),?_,?_⟩
  · simpa only [ha.mem] using hf
  · simpa only [ha.mem] using hpair

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
