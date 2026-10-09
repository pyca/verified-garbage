import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitial
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecond
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallMath

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf W)

 theorem whole_bytes (σ : State) : Sample.Ball.X σ=firstBytes σ++tailBytes σ := by
  change Spec.MlDsa.H _ 272=Spec.MlDsa.H _ 136++_
  rw [H_eq,H_eq]
  exact squeeze_split _

 theorem branch_ok (v : Proof.Sha3.AArch64.Permutation) {σ s : State}
    (hp : sbK.pre σ) (h : Initial σ s) :
    WP isa (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      s (Sample.Ball.LP σ) := by
  have ht : tauOf σ≤64 := by have := (Sample.Ball.params hp).2.2; omega
  have hl : (firstBytes σ).length=136 := H_length _ _
  have hi : (ballFold (tauOf σ) (firstBytes σ)).2≤256 := bFold_le (by simp only [Spec.MlDsa.n]; omega) _
  have hg : 256-tauOf σ≤(ballFold (tauOf σ) (firstBytes σ)).2 := by
    simpa only [ballFold,Spec.MlDsa.n] using (bFold_ge (τ := tauOf σ) (h := signs (firstBytes σ)) (Vector.replicate 256 0,256-tauOf σ) ((firstBytes σ).drop 8))
  by_cases hd : (ballFold (tauOf σ) (firstBytes σ)).2=256
  · refine WP.ite true (by rw [eval_zero,eq_zero_iff,h.parser.x11,hd]; rfl) (fun _ => wp_nil ?_) (fun hh => nomatch hh)
    have heq : ballFold (tauOf σ) (Sample.Ball.X σ)=ballFold (tauOf σ) (firstBytes σ) := by
      rw [whole_bytes]; exact fold_append_done (by rw [hl]; decide) hd _
    refine ⟨h.env,?_,?_⟩
    · rw [heq]; exact h.parser.x10
    · rw [heq]; exact h.parser.stored
  · refine WP.ite (M := isa) false (by rw [eval_zero,eq_zero_iff,h.parser.x11]; simp only [decide_eq_false_iff_not, Option.some.injEq]; omega) (fun hh => nomatch hh) (fun _ => ?_)
    refine WP.mono (second_ok v (τ := tauOf σ) (h := signs (firstBytes σ)) (Sample.Ball.spOk hp) h.env h.parser hi
      (Proof.Sha3.length_squeezeFrom (by decide) (by decide) _ _ _)
      h.pos h.next (fun j hj hjn => ?_)) fun u hu => ?_
    · rw [← BitVec.shiftRight_add]
      rw [show (ballFold (tauOf σ) (firstBytes σ)).2-(256-tauOf σ)+
        (j-(ballFold (tauOf σ) (firstBytes σ)).2)=j-(256-tauOf σ) from by omega]
      exact Sample.Ball.sign_bit (by omega) (by omega) hjn ht
    · have heq : ballFold (tauOf σ) (Sample.Ball.X σ)=
          bFold (tauOf σ) (signs (firstBytes σ)) (ballFold (tauOf σ) (firstBytes σ)) (tailBytes σ) := by
        rw [whole_bytes,fold_append_bytes _ (by rw [hl]; decide)]
      exact ⟨hu.env,heq.symm ▸ hu.parser.x10,heq.symm ▸ hu.parser.stored⟩

 theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : sbK.pre σ) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee) σ
      (fun u => abiPreserved σ u ∧ sbK.post σ u) := by
  refine WP.seq (WP.mono (Sample.Ball.pro_ok hp) fun _ h0 =>
    WP.seq (WP.mono (spongeResume_ok (Sample.Ball.spOk hp) v (rate := 136) (outlen := 136)
      (by decide) (by decide) h0) fun s h1 => ?_))
  have hc := WP.mono (initial_ok hp h1) fun t ht =>
    WP.seq (WP.mono (branch_ok v hp ht) fun u hu => Sample.Ball.end_ok hp hu)
  exact WP.assoc (WP.seq hc)
end VG.Proof.MlDsa.AArch64.Optimized.Ball
