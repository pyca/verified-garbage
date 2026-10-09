import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitial
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirstTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf)

theorem zero_ready {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa Impl.MlDsa.AArch64.Optimized.Ball.zeroWide s fun u =>
      Keep [] s u ∧ FirstReady (spOf σ).a ((spOf σ).at' 840) (tauOf σ) (firstBytes σ) u := by
  have ps := Sample.Ball.spOk hp
  refine WP.mono (zeroWide_coeffs h.first.env.x26 (fun i hi => ?_)) fun t ⟨kt,ft,hz⟩ => ?_
  · rw [h.first.env.wr,ps.wr]
    exact in_regions (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have et := h.first.env.keepA ps kt ft
  have ot : bytesAt t.mem ((spOf σ).at' 840) 136=firstBytes σ := by
    rw [MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' ps (by decide)).symm) (by decide),h.first.out]
    exact (H_eq _ _).symm
  refine ⟨kt,by rw [et.x25]; rfl,et.x26,?_,?_,hz,?_,?_⟩
  · rw [et.x27]; simp [tauOf]; omega
  · intro j hj
    rw [← ot,MlKem.bytesAt_getD _ _ hj]
  · rw [regions ps et]
    refine Covers.of_sub fun r hr => ?_
    rcases mem2 hr with rfl|rfl
    · exact ⟨(spOf σ).scrR,by simp,840,rfl,by simp⟩
    · exact ⟨polyR (spOf σ).a,by simp,0,(ptr_zero _).symm,by simp⟩
  · rw [et.wr,ps.wr]
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨polyR (spOf σ).a,by simp,0,(ptr_zero _).symm,by simp⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
