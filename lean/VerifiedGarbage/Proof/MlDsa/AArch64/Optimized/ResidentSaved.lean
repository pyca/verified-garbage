import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG

/-! ## From `ResidentEpi.lean` -/

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
    simpa only [show 7968+8*(i+1)=7976+8*i by omega] using hrg (i+1) (by omega))) ?_
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
      simpa only [show 7968+8*(i+1)=7976+8*i by omega] using hs.gpr (i+1) (by omega)
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
        (by omega) (by omega) (by decide)) hd (by decide)]
    exact h.gpr i hi
  · intro i hi
    rw [hf.readW (r := ⟨base+7968,144⟩)
      (Offset.contains base (d := 8048+8*i) (e := 7968) (n := 8) (k := 144)
        (by omega) (by omega) (by decide)) hd (by decide)]
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
        (by omega) (by omega) (by decide)) (by
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
