import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPro

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Restores every nonvolatile vector from the untouched save area. -/
theorem restoreV_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<8, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block restore) s fun t => RegKeep [] s t ∧ t.mem=s.mem ∧
      ∀i<8,t.v (vreg (8+i))=σ.v (vreg (8+i)) := by
  unfold restore
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.mem=s.mem ∧ ∀i<k,t.v (vreg (8+i))=σ.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => by omega⟩
  refine wp_ldrq ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.vupd hu)).mono (by simp),hu.mem.trans ht.2.1,?_⟩
  intro i hi
  by_cases he : i=k
  · subst i
    rw [hu.v,ht.2.1,hs.vec k hk]
  · have hne : vreg (8+i)≠vreg (8+k) := by
      rw [ne_eq,vreg_inj (8+i) (by omega) (8+k) (by omega)]; omega
    rw [hu.get _ hne]
    exact ht.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
