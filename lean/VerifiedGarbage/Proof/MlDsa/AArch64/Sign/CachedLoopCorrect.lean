import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached commitment has the ordinary commitment result and prepares
exactly the odd mask of the next attempt. -/
def CommitCorrect (P : Prims) (p : Params) (S : Nat) : Prop :=
  ∀σ s t,PositiveIL p S σ t s → PairedRoots S s → (t=0 ∨ Mask p σ t s) →
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s fun u=>
      PositiveIC p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u

theorem iter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) (roots : PairedRoots S s)
    (cache : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveLP p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  refine WP.seq (WP.mono (hcommit σ s t h roots cache) fun a ⟨ha,ra,ca⟩=>?_)
  refine WP.seq (WP.mono (CachedChecks.ball_ok hP hp hb ⟨ra,ca⟩ ha) fun b ⟨hball,rb⟩=>?_)
  refine WP.seq (WP.ite (M:=isa) _ (eval_w0 b) (fun he=>?_) fun he=>?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e|e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    refine WP.mono (CachedChecks.checks_ok hp (ksChk_ok hp) rb.roots hball h1 rb.cache)
      fun u ⟨hu,ru,cu⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ⟨ru,cu⟩
      (hu.elim .inl (fun h=>.inr (.inl h)))) fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩
  · refine WP.mono (CachedChecks.ballFailure_ok hp (lChk_ok hp) rb hball (by simpa using he))
      fun u ⟨hu,ru⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ru (.inr (.inr hu)))
      fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩

/-- The first attempt samples its own mask. Every later attempt receives the
cached mask preserved through all checks and the counter decrement. -/
theorem signLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine WP.seq (WP.mono (WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    fun a ⟨ha,ra⟩=>?_)
  refine WP.loop (M:=isa)
    (fun n s=>∃t,n=814-t ∧ PositiveIL p S σ t s ∧ PairedRoots S s ∧ (t=0 ∨ Mask p σ t s))
    (fun n s ⟨t,hn,hs,rs,cs⟩=>?_) 814 a ⟨0,rfl,ha,ra,.inl rfl⟩
  refine WP.mono (iter_ok hP hp hb hcommit hs rs cs) fun u ⟨hu,ru,cu⟩=>?_
  rcases hu with ⟨hz,hi⟩|⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega,
      t+1,rfl,hi,ru,.inr cu⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx,ru⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached
