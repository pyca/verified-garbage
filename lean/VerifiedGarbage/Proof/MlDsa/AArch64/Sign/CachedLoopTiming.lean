import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopTrace
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopCache

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The original leakage relation remains unchanged. Cache correctness is
an invariant of each execution, not additional observable information. -/
theorem iter_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (fun x y=>PairedIX p S t x y ∧ CacheHeld p S (t+1) x ∧ CacheHeld p S (t+1) y) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  have hchecks : PairedChecksCT p S (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
    intro t ht
    apply positivePairedChecks_tr hp3 (ksChk_ok hp3) h16 hP.s64
    intro σ τ he hs ht'
    exact leq_pass (paramsOk hp3) he ht hs ht'
  intro x y tx ty x' y' hr ex ey
  obtain ⟨eq,hi⟩ := iter_trace hP hp hchecks hcommit hball ht _ _ _ _ _ _ hr ex ey
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := hr.1.1
  obtain ⟨_,u,eu,hu,ru,cu⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hx.1.1 hx.2 hx.1.2
  obtain ⟨_,v,ev,hv,rv,cv⟩ := iter_ok hP hp3 (bChk_ok hp3) (commit_correct hP hp hcommit)
    hy.1.1 hy.2 hy.1.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨eq,hi,cacheHeld_of (PositiveLP.key hu) cu,cacheHeld_of (PositiveLP.key hv) cv⟩

theorem signLoop_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) (h16 : 16≤S)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p 0) (PositiveIK p S))
      (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      (PositiveOX p S) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine RelCT.seq (liftPairedR (J:=fun σ s=>PositiveIL p S σ 0 s)
    (fun _ _ _ h roots=>WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp3) h) roots (Nat.zero_le _) hP.s64)
    (lrel_tr (fun _ _ h=>h.root.1.lrel (fun _ _ h=>h.d.im.st)) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M:=isa)
    (fun n x y=>∃t,n=814-t ∧ PairedRS p S (LeakEq p t)
      (fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s)) x y)
    (fun n=>?_) 814)
    (fun _ _ h=>⟨0,rfl,h.mono (fun _ _ h=>⟨h,.inl rfl⟩)⟩) (fun _ _ h=>h)
  intro x y tx ty x' y' ⟨t,hn,hr⟩ ex ey
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,hx,_⟩ := hr.1.1; exact hx.1.1.t_lt
  obtain ⟨htr,hi,cx,cy⟩ := iter_tr hP hp h16 hcommit hball ht _ _ _ _ _ _ hr ex ey
  refine ⟨htr,by rw [eval_x9,eval_x9,hi.1.1],fun h=>hi.1.2.2 (x9_zero h),fun h=>?_⟩
  have hnxt := hi.next (x9_ne h)
  obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hnxt
  exact ⟨814-(t+1),by omega,t+1,rfl,
    ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,.inr (cx σ hx.1.k)⟩,hx.2⟩,
      ⟨⟨hy.1,.inr (cy τ hy.1.k)⟩,hy.2⟩⟩,rs⟩,rp⟩⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached
