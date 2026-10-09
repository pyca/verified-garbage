import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample

/-- The resident implementation retains the established bounded sampler result. -/
theorem prefixRow_legacy (σ : State) (k : Nat) :
    prefixRow σ k 1008=VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k := by
  unfold prefixRow
  rw [streamBytes_full]

theorem result_legacy {σ t : State} (h : Result 4 σ t) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.post σ t := by
  constructor
  · rw [h.status]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.mask
    have he : ((List.range 4).all fun k =>
        (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length==256)=true ↔
        ∀k<4,(prefixRow σ k 1008).length=256 := by
      simp only [List.all_eq_true,List.mem_range,beq_iff_eq,prefixRow_legacy]
    by_cases hall : ∀k<4,(prefixRow σ k 1008).length=256
    · rw [ite_eq_left hall,ite_eq_left (he.mpr hall)]
      rfl
    · rw [ite_eq_right hall,ite_eq_right (fun hh => hall (he.mp hh))]
      rfl
  · intro k hk hl
    exact stored_polyIs (by simpa only [prefixRow_legacy,polyP,VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP] using h.stored k hk) hl

theorem pre_four {σ : State} (h : (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre σ) : Pre 4 σ := by
  obtain ⟨hr,hw,hsa,hss,has⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_pre σ h
  exact ⟨Or.inr rfl,hr,hw,hsa,hss,has⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
