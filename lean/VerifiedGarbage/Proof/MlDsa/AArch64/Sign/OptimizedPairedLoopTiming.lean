import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedBallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopEndTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopCorrect

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : Proof.Sha3.AArch64.Permutation}

def PairedChecksCT (p : Params) (S : Nat) (checks : Prog isa) : Prop :=
  ∀t,t<814 → RelCT isa
    (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
    checks (PairedRS p S (LeakEq p t) fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s)

theorem pairedIter_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveIL p S · t))
      (Impl.MlDsa.AArch64.Sign.Optimized.iterWith keccak.callee P p checks) (PairedIX p S t) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.iterWith
  refine RelCT.seq (pairedCommit_tr hP hp hcommit) (RelCT.seq (pairedBall_step_tr hP hp ht hball) ?_)
  refine RelCT.seq (R:=fun x y=>
      (PairedRS p S (LeakEq p t) (fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s) x y ∧ True) ∨
      (PairedRS p S (LeakEq p t) (PositiveEB p S · t) x y ∧ True))
    (RelCT.ite ?_ ?_ ?_)
    (relOr (RelCT.mono (pairedEndPF_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h))
      (RelCT.mono (pairedEndB_tr hp hP.s64) (fun _ _ h=>h.1) (fun _ _ h=>h)))
  · rintro x y ⟨_,he⟩; rw [eval_w0,eval_w0,he]
  · refine RelCT.mono (hchecks t ht) ?_ (fun _ _ h=>.inl ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h1 := x0_one hx.1.r01 hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h1⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h1⟩,hy.2⟩⟩,rs⟩,rp⟩
  · have hf : RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=0)
        (.block (([.movz .x .x24 0 0] : List Instr)++setQ (VG.Impl.MlDsa.AArch64.Call.sc oCNT) 1))
        (PairedRS p S (LeakEq p t) (PositiveEB p S · t)) :=
      RelCT.mono (paired_trace_frame (Nat.zero_le _) hP.s64 (positiveBallFailure_tr hp (lChk_ok hp)))
        (fun _ _ h=>h) (fun _ _ h=>PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2)
    refine RelCT.mono hf ?_ (fun _ _ h=>.inr ⟨h,trivial⟩)
    rintro x y ⟨⟨hr,eq⟩,hb⟩
    obtain ⟨⟨⟨σ,τ,ps,pt,pub,he,hx,hy⟩,rs⟩,rp⟩ := hr
    have h0 := x0_zero hb
    exact ⟨⟨⟨σ,τ,ps,pt,pub,he,⟨⟨hx.1,h0⟩,hx.2⟩,⟨⟨hy.1,eq.symm.trans h0⟩,hy.2⟩⟩,rs⟩,rp⟩

theorem pairedSignLoop_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Optimized.commitWith keccak.callee P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S) :
    RelCT isa (PairedRS p S (LeakEq p 0) (PositiveIK p S))
      (Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith keccak.callee P p checks) (PositiveOX p S) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signLoopWith
  refine RelCT.seq (liftPairedR (J:=fun σ s=>PositiveIL p S σ 0 s)
    (fun _ _ _ h roots=>WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    (lrel_tr (fun _ _ h=>h.root.1.lrel (fun _ _ h=>h.d.im.st)) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M:=isa)
    (fun n x y=>∃t,n=814-t ∧ PairedRS p S (LeakEq p t) (PositiveIL p S · t) x y)
    (fun n=>?_) 814) (fun _ _ h=>⟨0,rfl,h⟩) (fun _ _ h=>h)
  intro x y tx ty x' y' ⟨t,hn,hr⟩ ex ey
  have ht : t<814 := by obtain ⟨_,_,_,_,_,_,hx,_⟩ := hr.1.1; exact hx.1.t_lt
  obtain ⟨htr,hi⟩ := pairedIter_tr hP hp hchecks hcommit hball ht _ _ _ _ _ _ hr ex ey
  exact ⟨htr,by rw [eval_x9,eval_x9,hi.1.1],fun h=>hi.1.2.2 (x9_zero h),
    fun h=>⟨814-(t+1),by omega,t+1,rfl,hi.next (x9_ne h)⟩⟩

end VG.Proof.MlDsa.AArch64.Sign
