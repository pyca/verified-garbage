import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSaveV

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem low_setLane (v : BitVec 128) (a : BitVec 64) :
    vdword (setLane v 64 0 a) 0=a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,setLane,BitVec.getLsbD_extractLsb',BitVec.getLsbD_or,
    BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi,decide_eq_true]

private theorem restoreV_step (s : State) {i : Nat} (hi : i<8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) s
      fun t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
        vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64 ∧
        ∀ r, r≠vreg (8+i) → t.v r=s.v r := by
  refine wp_ldr ⟨by omega,by omega⟩ rfl hin fun u h1 => ?_
  refine wp_vop (d := vreg (8+i)) rfl fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).mono (by simp)
  · exact h2.mem.trans h1.mem
  · rw [h2.v,low_setLane,h1.gpr]
  · intro r hr; rw [h2.other r hr,h1.vec]

/-- Restore precisely the ABI-preserved low halves of v8 through v15. -/
theorem restoreV_ok (s : State)
    (hr : ∀ i<8, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)])) s
      fun t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
        ∀ i<8, vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
      ∀ i<k, vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64)
    (fun k t hk ⟨ht,hm,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (restoreV_step t hk (by rw [ht.rd,ht.wr,ht.gpr .x19 (by decide)]; exact hr k hk)) ?_
  intro u ⟨hu,hmu,hvu,hother⟩
  refine ⟨(ht.trans hu).mono (by simp),hmu.trans hm,fun i hi => ?_⟩
  by_cases heq : i=k
  · subst i; rw [hvu,hm,ht.gpr .x19 (by decide)]
  · rw [hother (vreg (8+i)) (fun he => heq (by
      have hv := (vreg_inj (8+i) (by omega) (8+k) (by omega)).mp he
      omega))]
    exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
