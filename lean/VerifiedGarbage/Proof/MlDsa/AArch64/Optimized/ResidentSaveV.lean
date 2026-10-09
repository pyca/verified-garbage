import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSaveG

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_str WP.cons)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem saveV_step (s : State) {i : Nat} (hi : i<8)
    (hw : InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)]) s fun t =>
      RegKeep [.x8] s t ∧ t.v=s.v ∧
      t.mem=s.mem.writeW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) (vdword (s.v (vreg (8+i))) 0) := by
  refine WP.cons (s' := s.write .x .x8 (vdword (s.v (vreg (8+i))) 0)) rfl ?_
  have h1 := Upd.write64 s .x8 (vdword (s.v (vreg (8+i))) 0)
  refine wp_str ⟨by omega,by omega⟩ (by rw [h1.other .x4 (by decide)])
    (by rw [h1.wr]; exact hw) fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (RegKeep.upd h1).trans (RegKeep.mupd h2) |>.mono (by simp)
  · exact h2.vec.trans h1.vec
  · rw [h2.mem,h1.mem,h1.gpr]

theorem saveV_ok (s : State)
    (hw : ∀ i<8, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)])) s fun t =>
      RegKeep [.x8] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x4+8048,64⟩] s.mem t.mem ∧
      ∀ i<8, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 64=vdword (s.v (vreg (8+i))) 0 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x4+8048,64⟩] s.mem t.mem ∧
      ∀ i<k, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 64=vdword (s.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (saveV_step t hk (by rw [ht.wr,ht.gpr .x4 (by decide)]; exact hw k hk)) ?_
  intro u ⟨hu,hvu,hm⟩
  rw [ht.gpr .x4 (by decide)] at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (s.gpr .x4) (d := 8048+8*k) (e := 8048) (n := 8) (k := 64)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x4)
        (d := 8048+8*i) (e := 8048+8*k) (n := 8) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
