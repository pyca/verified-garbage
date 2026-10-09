import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopConcrete

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem iter_trace {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp0 : p=mlDsa65 ∨ p=mlDsa87) {checks : Prog isa} (hchecks : PairedChecksCT p S checks)
    (hcommit : 16*(Impl.MlDsa.AArch64.Sign.Cached.commit P p).aarch64Depth≤S)
    (hball : 16*(ballAt P (cLen p) p.τ cP).aarch64Depth≤S)
    {t : Nat} (ht : t<814) :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.iter P p checks) (PairedIX p S t) := by
  have hp : Ok3 p := by rcases hp0 with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  have hct : RelCT isa
      (PairedRS p S (LeakEq p t) fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.commit P p)
      (PairedRS p S (LeakEq p t) (PositiveIC p S · t)) :=
    RelCT.mono (paired_trace_frame hcommit hP.s64 (commit_tr hP hp0))
      (fun _ _ h=>h) (fun _ _ h=>(PairedRS.of_root h.1 h.2.1 h.2.2.1 h.2.2.2).mono (fun _ _ h=>h.1))
  refine RelCT.seq hct (RelCT.seq (pairedBall_step_tr hP hp ht hball) ?_)
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


end VG.Proof.MlDsa.AArch64.Sign.Cached
