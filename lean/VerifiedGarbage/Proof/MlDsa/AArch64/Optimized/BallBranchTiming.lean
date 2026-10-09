import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitialTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq W)

 theorem branch_timing (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee) :
    RelCT isa (CursorPair Initial)
      (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      (fun _ _ => True) := by
  refine RelCT.ite (fun s t hh => ?_) ?_ ?_
  · obtain ⟨σ₁,σ₂,_,_,hq,h₁,h₂,_⟩ := hh
    rw [eval_zero,eval_zero,eq_zero_iff,eq_zero_iff,h₁.parser.x11,h₂.parser.x11,tau_eq hq,first_eq hq]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun s t hh => by
      obtain ⟨⟨σ₁,σ₂,_,_,hq,h₁,h₂,_⟩,_⟩ := hh
      exact agree_of (by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1]) (by simp)) (by taint_decide)
  · intro s t ts tt u z ⟨⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,h0⟩,_⟩ es et
    have ht : tauOf σ₁≤64 := by have := (Sample.Ball.params p₁).2.2; omega
    have hg : 256-tauOf σ₁≤(ballFold (tauOf σ₁) (firstBytes σ₁)).2 := by
      simpa only [ballFold,Spec.MlDsa.n] using (bFold_ge (τ := tauOf σ₁) (h := signs (firstBytes σ₁)) (Vector.replicate 256 0,256-tauOf σ₁) ((firstBytes σ₁).drop 8))
    have hs₂ : SpOk (spOf σ₁) σ₂ := by rw [pub_eq hq]; exact Sample.Ball.spOk p₂
    have e₂ : Env (spOf σ₁) σ₂ t := by rw [pub_eq hq]; exact h₂.env
    have pp₂ := h₂.parser
    rw [← pub_eq hq,← tau_eq hq,← first_eq hq] at pp₂
    have nx₂ := h₂.next
    rw [← pub_eq hq,← tail_eq hq] at nx₂
    exact second_relCT v hc (τ := tauOf σ₁) (h := signs (firstBytes σ₁))
      (i := (ballFold (tauOf σ₁) (firstBytes σ₁)).2)
      (c := (ballFold (tauOf σ₁) (firstBytes σ₁)).1)
      (w := W (firstBytes σ₁) >>> ((ballFold (tauOf σ₁) (firstBytes σ₁)).2-(256-tauOf σ₁)))
      (Y := tailBytes σ₁)
      (Sample.Ball.spOk p₁) hs₂ (bFold_le (by simp only [Spec.MlDsa.n]; omega) _)
      (Proof.Sha3.length_squeezeFrom (by decide) (by decide) _ _ _)
      (fun j hj hjn => by
        rw [← BitVec.shiftRight_add]
        rw [show (ballFold (tauOf σ₁) (firstBytes σ₁)).2-(256-tauOf σ₁)+
          (j-(ballFold (tauOf σ₁) (firstBytes σ₁)).2)=j-(256-tauOf σ₁) from by omega]
        exact Sample.Ball.sign_bit (by omega) (by omega) hjn ht)
      s t ts tt u z
      ⟨⟨h₁.env,h₁.parser,h₁.pos,h₁.next⟩,⟨e₂,pp₂,h₂.pos,nx₂⟩,
        by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1],h0⟩ es et

 theorem branch_step (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee) :
    RelCT isa (CursorPair Initial)
      (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      (Rel2 sbK.pre sbK.pub Sample.Ball.LP) := by
  intro s t ts tt u z hh es et
  have he := branch_timing v hc _ _ _ _ _ _ hh es et
  obtain ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,_⟩ := hh
  obtain ⟨_,_,e₁,f₁⟩ := branch_ok v p₁ h₁
  obtain ⟨_,_,e₂,f₂⟩ := branch_ok v p₂ h₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  exact ⟨he.1,σ₁,σ₂,p₁,p₂,hq,f₁,f₂⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
