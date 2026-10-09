import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem pairedIter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    (hchecks : ∀σ s t,PositiveIB p S σ t s → PairedRoots S s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks)
      s fun u=>PositiveLP p S σ t u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine WP.seq (WP.mono (WP.pairedRoots (positiveCommit_ok hP hp h) roots hcommit hP.s64) fun a ⟨ha,ra⟩ => ?_)
  refine WP.seq (WP.mono (WP.pairedRoots (positiveBall_ok hP hp hb ha) ra hball hP.s64) fun b ⟨hball,rb⟩ => ?_)
  refine WP.seq (WP.ite (M := isa) _ (eval_w0 b) (fun he => ?_) fun he => ?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e | e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    refine WP.mono (hchecks σ b t hball rb h1) fun u ⟨hu,ru⟩ => ?_
    exact WP.pairedRoots (positiveDecEnd hp (paramsOk hp) (lChk_ok hp)
      (hu.elim .inl (fun h => .inr (.inl h)))) ru (Nat.zero_le _) hP.s64
  · refine WP.mono (WP.pairedRoots (positiveBallFailure_ok hp (lChk_ok hp) hball (by simpa using he))
      rb (Nat.zero_le _) hP.s64) fun u ⟨hu,ru⟩ => ?_
    exact WP.pairedRoots (positiveDecEnd hp (paramsOk hp) (lChk_ok hp) (.inr (.inr hu)))
      ru (Nat.zero_le _) hP.s64

theorem pairedSignLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) {checks : Prog isa}
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    (hchecks : ∀σ s t,PositiveIB p S σ t s → PairedRoots S s → (s.gpr .x0).setWidth 32=1 →
      WP isa checks s fun u => (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks)
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine WP.seq (WP.mono (WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    fun a ⟨ha,ra⟩ => ?_)
  refine WP.loop (M := isa) (fun n s => ∃t,n=814-t ∧ PositiveIL p S σ t s ∧ PairedRoots S s)
    (fun n s ⟨t,hn,hs,rs⟩ => ?_) 814 a ⟨0,rfl,ha,ra⟩
  refine WP.mono (pairedIter_ok hP hp hb hcommit hball hchecks hs rs) fun u ⟨hu,ru⟩ => ?_
  rcases hu with ⟨hz,hi⟩ | ⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega,t+1,rfl,hi,ru⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx,ru⟩

end VG.Proof.MlDsa.AArch64.Sign
