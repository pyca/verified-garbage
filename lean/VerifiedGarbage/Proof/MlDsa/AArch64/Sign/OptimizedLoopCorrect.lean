import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem positiveIter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hchecks : ∀σ s t,PositiveIB p S σ t s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => PositiveEP p S σ t u ∨ PositiveEF p S σ t u)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks)
      s (PositiveLP p S σ t) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine WP.seq (WP.mono (positiveCommit_ok hP hp h) fun a ha => ?_)
  refine WP.seq (WP.mono (positiveBall_ok hP hp hb ha) fun b hball => ?_)
  refine WP.seq (WP.ite (M := isa) _ (eval_w0 b) (fun he => ?_) fun he => ?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e | e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    exact WP.mono (hchecks σ b t hball h1) fun u hu =>
      positiveDecEnd hp (paramsOk hp) (lChk_ok hp) (hu.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (positiveBallFailure_ok hp (lChk_ok hp) hball (by simpa using he)) fun u hu =>
      positiveDecEnd hp (paramsOk hp) (lChk_ok hp) (.inr (.inr hu))

/-- Phase composition preserves the original 814-attempt bound and exact
success/failure semantics. The checks premise is discharged by the response phases. -/
theorem positiveSignLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hchecks : ∀σ s t,PositiveIB p S σ t s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => PositiveEP p S σ t u ∨ PositiveEF p S σ t u)
    {σ s : State} (h : PositiveIK p S σ s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks)
      s (PositiveXS p S σ) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine WP.seq (WP.mono (positiveLoopInit_ok (lChk_ok hp) h) fun a ha => ?_)
  refine WP.loop (M := isa) (fun n s => ∃t,n=814-t ∧ PositiveIL p S σ t s)
    (fun n s ⟨t,hn,hs⟩ => ?_) 814 a ⟨0,rfl,ha⟩
  refine WP.mono (positiveIter_ok hP hp hb hchecks hs) fun u hu => ?_
  rcases hu with ⟨hz,hi⟩ | ⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega,t+1,rfl,hi⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx⟩

end VG.Proof.MlDsa.AArch64.Sign
