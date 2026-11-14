module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.AArch64.Optimized.ResidentAbsorbArgs`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.ResidentSaved`, which only this module used -/

section

/-! ## From `ResidentEpi.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_ldrx)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (epi saved)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

structure Saved (s : State) (base : Addr) (m : Mem) : Prop where
  gpr : ∀ i<10, m.readW (base+BitVec.ofNat 64 (7968+8*i)) 64=s.gpr (saved[i]!)
  vec : ∀ i<8, m.readW (base+BitVec.ofNat 64 (8048+8*i)) 64=vdword (s.v (vreg (8+i))) 0

/-- The scratch-tail epilogue restores the standard AArch64 ABI. No private
calling convention is exposed by the inline resident permutation. -/
theorem epi_ok (σ s : State) (base : Addr) (hbase : s.gpr .x19=base)
    (hsp : s.sp=σ.sp) (hlr : s.gpr .x30=σ.gpr .x30) (hs : Saved σ base s.mem)
    (hrg : ∀ i<10, InRegions (s.rd++s.wr) (base+BitVec.ofNat 64 (7968+8*i)) 8)
    (hrv : ∀ i<8, InRegions (s.rd++s.wr) (base+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr := by
  unfold epi
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (restoreV_ok s (by simpa only [hbase] using hrv)) ?_
  intro a ⟨ha,ham,hav⟩
  have a19 : a.gpr .x19=base := (ha.gpr .x19 (by decide)).trans hbase
  rw [WP.block_append_iff]
  refine WP.mono (restoreG_ok a (fun i hi => by
    rw [ha.rd,ha.wr,a19]
    simpa only [show 7968+8*(i+1)=7976+8*i by omega_using []] using hrg (i+1) (by omega_using [hi]))) ?_
  intro b ⟨hb,hbg⟩
  refine wp_ldrx (a := base+BitVec.ofNat 64 7968) ⟨by decide,by decide⟩
    (by rw [hb.get .x19,a19])
    (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hrg 0 (by decide))
    fun t ht htg => WP.block_nil_iff.mpr ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro r hr
    have hp : ∀ r ∈ preserved, r=.x19 ∨ r=.x30 ∨ ∃ i<9, r=saved[i+1]! := by decide
    rcases hp r hr with rfl | rfl | ⟨i,hi,rfl⟩
    · rw [htg,hb.mem,ham]
      exact hs.gpr 0 (by decide)
    · rw [ht.get .x30,hb.get .x30,ha.gpr .x30 (by decide),hlr]
    · have hn : saved[i+1]! ≠ Reg.x19 := by
        have hn : ∀ j<9, saved[j+1]! ≠ Reg.x19 := by decide
        exact hn i hi
      rw [ht.get (saved[i+1]!) (by simpa only [List.mem_singleton] using hn),hbg i hi,
        ham,ha.gpr .x19 (by decide),hbase]
      simpa only [show 7968+8*(i+1)=7976+8*i by omega_using []] using hs.gpr (i+1) (by omega_using [hi])
  · exact ht.sp.trans (hb.sp.trans (ha.sp.trans hsp))
  · intro v hv
    have hp : ∀ v ∈ preservedV, ∃ i<8, v=vreg (8+i) := by decide
    obtain ⟨i,hi,rfl⟩ := hp v hv
    rw [ht.vcs _ hv,hb.vcs _ hv]
    change vdword (a.v (vreg (8+i))) 0=vdword (σ.v (vreg (8+i))) 0
    rw [hav i hi,hbase]
    exact hs.vec i hi
  · exact ht.mem.trans (hb.mem.trans ham)
  · exact ht.rd.trans (hb.rd.trans ha.rd)
  · exact ht.wr.trans (hb.wr.trans ha.wr)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentSaved.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (saved)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Arithmetic, absorption and output writes may touch scratch, provided the
144-byte saved-register tail remains disjoint from their frame. -/
theorem Saved.keep {σ : State} {base : Addr} {m m' : Mem} {rs : List Region}
    (h : Saved σ base m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (Region.mk (base+7968) 144).Disjoint r) : Saved σ base m' := by
  constructor
  · intro i hi
    rw [hf.readW (r := ⟨base+7968,144⟩)
      (Offset.contains base (d := 7968+8*i) (e := 7968) (n := 8) (k := 144)
        (by omega_using []) (by omega_using [hi]) (by decide)) hd (by decide)]
    exact h.gpr i hi
  · intro i hi
    rw [hf.readW (r := ⟨base+7968,144⟩)
      (Offset.contains base (d := 8048+8*i) (e := 7968) (n := 8) (k := 144)
        (by omega_using []) (by omega_using [hi]) (by decide)) hd (by decide)]
    exact h.vec i hi

/-- Capture all scalar and SIMD ABI values before the resident code runs. -/
theorem save_ok (s : State)
    (hg : ∀ i<10, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (7968+8*i)) 8)
    (hv : ∀ i<8, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block (((List.range 10).map fun i => .str .x (saved[i]!) .x4 (7968+8*i)) ++
      ((List.range 8).flatMap fun i => [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)]))) s
      fun t => RegKeep [.x8] s t ∧ Saved s (s.gpr .x4) t.mem ∧
        Frame [⟨s.gpr .x4+7968,144⟩] s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (saveG_ok s hg) ?_
  intro a ⟨ha,hfa,hga⟩
  refine WP.mono (saveV_ok a (by simpa only [ha.wr,ha.gpr] using hv)) ?_
  intro t ⟨ht,hvt,hft,hvalues⟩
  have hfb : Frame [⟨s.gpr .x4+8048,64⟩] a.mem t.mem := by simpa only [ha.gpr] using hft
  refine ⟨((RegKeep.mupd ha).trans ht).mono (by simp),⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hfb.readW (r := ⟨s.gpr .x4+7968,80⟩)
      (Offset.contains (s.gpr .x4) (d := 7968+8*i) (e := 7968) (n := 8) (k := 80)
        (by omega_using []) (by omega_using [hi]) (by decide)) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hga i hi
  · intro i hi
    simpa only [ha.gpr,ha.vec] using hvalues i hi
  · exact (hfa.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨⟨s.gpr .x4+7968,144⟩,by simp,Region.sub_prefix (by decide)⟩)).trans
      (hfb.sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨⟨s.gpr .x4+7968,144⟩,by simp,
          Offset.sub (s.gpr .x4) (d := 8048) (n := 64) (e := 7968) (k := 144) (by decide) (by decide)⟩))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

end

end


/-! ## From `ResidentZero.lean` -/

@[expose] public section

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
  refine wp_strq (a := wordAddr p k) (by omega_using [hk])
    (by rw [ht.gpr .x19 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega_using [hi, he])
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
  refine WP.mono (save_ok s (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => ⟨_,hw,Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)) ?_
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
    exact ⟨_,hin,Offset.contains_base _ hb (by omega_using [hb])⟩
  refine WP.mono (absorbBody_ok h2 h3 h4
    (fun j hj => input (8*j) 8 (by omega_using [hj]))
    (fun j hj => by
      change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 (8*j)) 8
      rw [Offset.add_add]; exact input (66+8*j) 8 (by omega_using [hj]))
    (input 64 1 (by decide)) (input 65 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 64) 1
        rw [Offset.add_add]; exact input (66+64) 1 (by decide))
    (by change InRegions _ (s.gpr .x20+BitVec.ofNat 64 66+BitVec.ofNat 64 65) 1
        rw [Offset.add_add]; exact input (66+65) 1 (by decide))
    (fun j hj => by rw [ha.wr]; exact ⟨_,hw,Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
    (hsep.sub_left (Region.sub_prefix (by decide)))
    (hsep.sub_left (Offset.sub_base _ (by decide)))
    (by simpa only [ha.mem] using hz)) ?_
  intro t ⟨ht,hf,hpair⟩
  refine ⟨((RegKeep.only ha).trans ht).mono (by simp),?_,?_⟩
  · simpa only [ha.mem] using hf
  · simpa only [ha.mem] using hpair

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

end

end

/-! ## From `ResidentMaskInit.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResidentParsePair.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

structure PairAccess (d : Nat) (s : State) : Prop where
  r0 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)) 16
  r1 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 16) 16
  r2 : ∀ off ∈ [840,1520], ∀ j<16, InRegions (s.rd++s.wr)
    (s.gpr .x19+BitVec.ofNat 64 off+BitVec.ofNat 64 (2*d*j)+BitVec.ofNat 64 (2*d-16)) 16
  w : ∀ p ∈ [Reg.x21,.x22], ∀ j<16, ∀ g<4, InRegions s.wr
    (s.gpr p+BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 (16*g)) 16
  sep : ∀ off ∈ [840,1520], ∀ p ∈ [Reg.x21,.x22],
    (Region.mk (s.gpr .x19+BitVec.ofNat 64 off) (32*d)).Disjoint ⟨s.gpr p,1024⟩
  outputs : (Region.mk (s.gpr .x21) 1024).Disjoint ⟨s.gpr .x22,1024⟩

structure PairParsed (d : Nat) (s t : State) : Prop where
  ready : ParseReady d t
  left : Parsed t.mem (s.gpr .x21) s.mem (s.gpr .x19+840) d 256
  right : Parsed t.mem (s.gpr .x22) s.mem (s.gpr .x19+1520) d 256
  frame : Frame [⟨s.gpr .x21,1024⟩,⟨s.gpr .x22,1024⟩] s.mem t.mem
  gpr : ∀ r, r≠.x0 → r≠.x4 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ v, v∉bodyTemps++initVectors → t.v v=s.v v
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Reuse the initialized constants for both independent SHAKE streams. -/
theorem parsePair_ready_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20)
    (hr : ParseReady d s) (hp : PairAccess d s) :
    WP isa (.seq (parse d .x21 840) (parse d .x22 1520)) s (PairParsed d s) := by
  apply WP.seq
  refine WP.mono (parse_ok s hd (by decide) (by decide) hr
    (hp.sep 840 (by decide) .x21 (by decide)) (hp.r0 840 (by decide))
    (hp.r1 840 (by decide)) (hp.r2 840 (by decide)) (hp.w .x21 (by decide))) ?_
  intro a ha
  have a19 := ha.gpr .x19 (by decide) (by decide) (by decide) (by decide)
  have a22 := ha.gpr .x22 (by decide) (by decide) (by decide) (by decide)
  refine WP.mono (parse_ok a hd (by decide) (by decide) ha.ready
    (by simpa only [a19,a22] using hp.sep 1520 (by decide) .x22 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r0 1520 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r1 1520 (by decide))
    (by simpa only [a19,ha.rd,ha.wr] using hp.r2 1520 (by decide))
    (by simpa only [a22,ha.wr] using hp.w .x22 (by decide))) ?_
  intro t ht
  have hf : Frame [⟨s.gpr .x22,1024⟩] a.mem t.mem := by simpa only [a22] using ht.frame
  refine ⟨ht.ready,?_,?_,?_,?_,?_,ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp⟩
  · exact ha.values.keep (by decide) hf (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.outputs)
  · intro i hi
    have hv := ht.values i hi
    rw [a22,a19] at hv
    rw [fieldValue_keep hd hi ha.frame (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.sep 1520 (by decide) .x21 (by decide))] at hv
    exact hv
  · exact (ha.frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (hf.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
  · intro r h0 h4 h9 h11
    exact (ht.gpr r h0 h4 h9 h11).trans (ha.gpr r h0 h4 h9 h11)
  · intro v hv
    have hvb : v∉bodyTemps := fun hm => hv (List.mem_append_left _ hm)
    exact (ht.vec v hvb).trans (ha.vec v hvb)

theorem PairAccess.keep {d : Nat} {s t : State} (h : PairAccess d s)
    (h19 : t.gpr .x19=s.gpr .x19) (h21 : t.gpr .x21=s.gpr .x21)
    (h22 : t.gpr .x22=s.gpr .x22) (hr : t.rd=s.rd) (hw : t.wr=s.wr) : PairAccess d t := by
  have hg : ∀ p ∈ [Reg.x21,.x22], t.gpr p=s.gpr p := by
    intro p hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact h21
    · exact h22
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [h19,hr,hw] using h.r0
  · simpa only [h19,hr,hw] using h.r1
  · simpa only [h19,hr,hw] using h.r2
  · intro p hp; simpa only [hg p hp,hw] using h.w p hp
  · intro off ho p hp; simpa only [h19,hg p hp] using h.sep off ho p hp
  · simpa only [h21,h22] using h.outputs

/-- Complete selected parser, including one-time shared vector constants. -/
theorem parseBoth_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) (hp : PairAccess d s) :
    WP isa (parseBoth d) s (PairParsed d s) := by
  unfold parseBoth
  apply WP.seq
  refine WP.mono (init_ok s hd) ?_
  intro a ha
  have h19 := ha.2.2.2.1 .x19 (by decide) (by decide)
  have h21 := ha.2.2.2.1 .x21 (by decide) (by decide)
  have h22 := ha.2.2.2.1 .x22 (by decide) (by decide)
  have hm := ha.2.2.2.2.2.1
  have hr := ha.2.2.2.2.2.2.1
  have hw := ha.2.2.2.2.2.2.2.1
  have hs := ha.2.2.2.2.2.2.2.2
  refine WP.mono (parsePair_ready_ok a hd ⟨ha.1,ha.2.1⟩ (hp.keep h19 h21 h22 hr hw)) ?_
  intro t ht
  refine ⟨ht.ready,?_,?_,?_,?_,?_,ht.rd.trans hr,ht.wr.trans hw,ht.sp.trans hs⟩
  · simpa only [h19,h21,hm] using ht.left
  · simpa only [h19,h22,hm] using ht.right
  · simpa only [h21,h22,hm] using ht.frame
  · intro r h0 h4 h9 h11
    exact (ht.gpr r h0 h4 h9 h11).trans (ha.2.2.2.1 r h9 h11)
  · intro v hv
    exact (ht.vec v hv).trans (ha.2.2.2.2.1 v (fun hm => hv (List.mem_append_right _ hm)))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
end

end

@[expose] public section

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
    exact h.frame.bytes (R := ⟨σ.gpr .x0,132⟩) (i := 66*p+i) hp.seedSep (by change 132≤2^64; decide) (by change 66*p+i<132; omega_using [hpn, hi])

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
    rw [ha.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)) ?_
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
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith core.code .x23 .x24 .x25 .x19) s (SpongePost σ) := by
  have hw (off len : Nat) (hb : off+len≤8192) :
      InRegions s.wr (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ hb (by omega_using [hb])⟩
  have hr (off len : Nat) (hb : off+len≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) len := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega_using [hb])⟩
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
    (fun i hi => hr (16*i) 16 (by omega_using [hi])) (fun i hi => hw (16*i) 16 (by omega_using [hi]))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega_using [hj, hi]))
    (fun j hj i hi => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 (16*i)) 16
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega_using [hj, hi]))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 840+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega_using [hj]))
    (fun j hj => by
      change InRegions _ (σ.gpr .x4+BitVec.ofNat 64 1520+BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 128) 8
      rw [Offset.add_add,Offset.add_add]; exact hw _ _ (by omega_using [hj]))
    (by decide) (by decide) (by decide) (by decide) (by rw [he.base])
    (fun k hk => by rw [Offset.add_add]; exact hw _ _ (by omega_using [hk]))
    (fun k hk => by rw [Offset.add_add]; exact hw _ _ (by omega_using [hk]))
    (Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))
    (Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))) ?_
  intro t ht
  have hk : RegKeep [.x6,.x7,.x15,.x16,.x24,.x25,.x28] s t := by
    refine ⟨?_,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.2.2.2.2.1 r hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.1
  refine ⟨he.lowStep hk ht.2.2.2.1 (by decide) ?_,ht.2.1,ht.2.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.sub_base _ (by decide)
  · exact Offset.sub_base _ (by decide)
  · exact Region.sub_prefix (by decide)
  · exact Offset.sub_base _ (by decide)

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
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega_using [hb])⟩
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
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega_using [hj]
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega_using [hj]
  · intro off hoff j hj
    rw [he.base,Offset.add_add,Offset.add_add]
    apply hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega_using [hj]
  · intro p hp' j hj g hg
    rw [Offset.add_add]
    exact ⟨_,hw p hp',Offset.contains_base _ (by omega_using [hj, hg]) (by omega_using [hj, hg])⟩
  · intro off hoff p hp'
    rw [he.base]
    refine (hs p hp').sub_left (Offset.sub_base _ ?_)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hoff
    rcases hoff with rfl | rfl <;> rcases hd with rfl | rfl <;> omega_using []
  · rw [he.out1,he.out2]; exact hp.outputs

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
