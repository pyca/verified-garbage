import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- Apply the final public hint-count bound after all strict norm checks. -/
theorem positiveOnesOk_ok {D : Nat} {p : Params} (hc : ksChk p = true)
    {σ : State} {t : Nat} {s : State} (h : PositiveIH p D σ t p.k s) :
    WP isa (.block (onesOk p)) s (PositiveKO p D σ t) := by
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ c13 _ _ c16 c17 _ _ _ _ hω _ hk _ _ _ => ?_
  obtain ⟨J6,h156⟩ := h
  have L6 := J6.b.l.st.lay
  have hS := onesSum_le (Hv p σ (p.ℓ*t)) p.k
  refine WP.mono_syms (onesOk_run p hω s (L6.inR c8)) fun s7 ⟨⟨h157,hm7⟩,k7⟩ hy => ?_
  rw [J6.ones,sign_bit (by omega) (by omega),h156,bit_and',bit_congr passV_iff] at h157
  have hP7 : PPostB D s s7 [] := postB_of_keep k7 (by decide) (by rw [hm7]; exact Frame.refl _ _)
  exact ⟨J6.b.step hP7 hy c13 (by simp),SignedFam.keep L6 hP7 c16 J6.z,
    HFam.keep L6 hP7 c17 J6.h,h157⟩

end VG.Proof.MlDsa.AArch64.Sign
