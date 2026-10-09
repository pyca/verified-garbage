import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentEpi

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
