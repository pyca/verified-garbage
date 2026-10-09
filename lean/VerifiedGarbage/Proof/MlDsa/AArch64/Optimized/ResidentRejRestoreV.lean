import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreV

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (restoreV oSave)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (restoreV_step)

theorem restoreV_with {v : Nat} {σ s : State} (he : Env v σ s)
    (hr : ∀d n,d+n≤8192 → InRegions (s.rd++s.wr) (at' σ d) n) :
    WP isa (.block restoreV) s fun t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < 8,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0 := by
  unfold restoreV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < k,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hm,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (restoreV_step hk ((ht.gpr .x19 (by decide)).trans he.x19)
    (by rw [ht.rd,ht.wr]; exact hr _ _ (by dsimp only [oSave]; omega)))
      fun u ⟨hu,hmu,hvu,hother⟩ => ?_
  refine ⟨(ht.trans hu).mono (by simp),hmu.trans hm,fun i hi => ?_⟩
  by_cases heq : i = k
  · subst i
    rw [hvu,hm]
    exact he.savedV k hk
  · rw [hother (vreg (8+i)) (fun h => heq (by
      have e := (vreg_inj (8+i) (by omega) (8+k) (by omega)).mp h
      omega))]
    exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
