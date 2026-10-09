import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- Timing of the full rejection-check phase, including the public success branch. -/
def PositiveChecksCT (p : Params) (D : Nat) (checks : Prog isa) : Prop :=
  ∀t,t<814 → RelCT isa
    (RootRS p D (LeakEq p t) fun σ s=>PositiveIB p D σ t s ∧ (s.gpr .x0).setWidth 32=1)
    checks (RootRS p D (LeakEq p t) fun σ s=>PositiveEP p D σ t s ∨ PositiveEF p D σ t s)

theorem positiveIter_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {checks : Prog isa} (hchecks : PositiveChecksCT p D checks)
    {t : Nat} (ht : t<814) :
    RelCT isa (RootRS p D (LeakEq p t) (PositiveIL p D · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks) (PositiveIX p D t) := by
  have hp := paramsOk h3
  have hc2 := bChk_ok h3
  have hc2' := hc2
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc2'
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine RelCT.seq (positiveCommit_tr hP h3) ?_
  refine RelCT.seq (R := fun x y=>RootRS p D (LeakEq p t) (PositiveIB p D · t) x y ∧
    (x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32) ?_ ?_
  · refine RelCT.mono (liftRootQ (G := fun _ _=>True) (J := fun σ s=>PositiveIB p D σ t s) (F := fun _ _=>True)
      (fun _ _ _ h=>WP.mono (positiveBall_ok hP h3 hc2 h) fun _ h=>⟨h,trivial⟩)
      (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h,_⟩=>⟨h.1.lrel (fun _ _ h=>h.c.masks.l.st),by
        obtain ⟨σ,τ,_,_,_,he,hx,hy⟩ := h.1
        rw [hx.ct,hy.ct]; exact leq_ct he ht⟩) (fun _ _ h=>h))
      (fun σ τ x y x' y' ps pt pub he _ _ _ jx jy _ _ eq roots=>
        ⟨⟨⟨σ,τ,ps,pt,pub,he,jx,jy⟩,roots⟩,eq⟩))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h)
  refine RelCT.seq (R := fun x y=>
      (RootRS p D (LeakEq p t) (fun σ s=>PositiveEP p D σ t s ∨ PositiveEF p D σ t s) x y ∧ True) ∨
      (RootRS p D (LeakEq p t) (PositiveEB p D · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_) (relOr (positiveEndPF_tr h3 hp (lChk_ok h3)) (positiveEndB_tr h3 hp (lChk_ok h3)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,roots⟩,eq⟩,hb⟩
    have h1 := x0_one hx.r01 hb
    exact ⟨⟨σ,τ,ps,pt,pub,he,⟨hx,h1⟩,⟨hy,eq.symm.trans h1⟩⟩,roots⟩
  · refine RelCT.mono (positiveBallFailure_tr h3 (lChk_ok h3)) ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,roots⟩,eq⟩,hb⟩
    have h0 := x0_zero hb
    exact ⟨⟨σ,τ,ps,pt,pub,he,⟨hx,h0⟩,⟨hy,eq.symm.trans h0⟩⟩,roots⟩

/-- The optimized loop retains the existing bounded-iteration leakage policy. -/
theorem positiveSignLoop_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (h3 : Ok3 p) {checks : Prog isa} (hchecks : PositiveChecksCT p D checks) :
    RelCT isa (RootRS p D (LeakEq p 0) (PositiveIK p D))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks) (PositiveOX p D) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine RelCT.seq (liftRootT (J := fun σ s=>PositiveIL p D σ 0 s) (fun _ _ h=>⟨h.d.im.st,h.d.roots⟩)
    (fun _ _ _ h=>positiveLoopInit_ok (lChk_ok h3) h)
    (lrel_tr (fun _ _ h=>h.1) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y=>∃t,n=814-t ∧ RootRS p D (LeakEq p t) (PositiveIL p D · t) x y)
    (fun n=>?_) 814) (fun _ _ h=>⟨0,rfl,h⟩) (fun _ _ h=>h)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t,hn,hr⟩ e₁ e₂
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,i₁,_⟩ := hr.1; exact i₁.t_lt
  obtain ⟨htr,hz,hc,ho⟩ := positiveIter_tr hP h3 hchecks ht _ _ _ _ _ _ hr e₁ e₂
  exact ⟨htr,by rw [eval_x9,eval_x9,hz],fun h=>ho (x9_zero h),
    fun h=>⟨814-(t+1),by omega,t+1,rfl,hc (x9_ne h)⟩⟩

end VG.Proof.MlDsa.AArch64.Sign
