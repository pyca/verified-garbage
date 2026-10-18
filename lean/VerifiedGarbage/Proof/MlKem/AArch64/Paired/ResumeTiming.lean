module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBothTiming

/-! # Fourth/fifth-block continuation branches only on the public matrix streams -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def StepTimingW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) : Prop :=
  ∀{s u : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c s → ProgressW w16 A B n p a b c u →
    s.syms "VG_MLKEM_REJ_SHUFFLE"=c → u.syms "VG_MLKEM_REJ_SHUFFLE"=c → s.sp=u.sp →
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraStep w16) (fun _ _=>True)

abbrev StepTiming := StepTimingW false

theorem bounded_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (step : StepTimingW w16 A B p a b c) (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (Impl.MlKem.AArch64.Paired.extraStep w16) (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraStep w16) (.block [])))
      (fun t v=>BoundedW w16 A B p a b c s t ∧ BoundedW w16 A B p a b c u v) := by
  let R := fun t v : State=>AdvancedW w16 A B 4 p a b c s t ∧ AdvancedW w16 A B 4 p a b c u v ∧
    t.syms=s.syms ∧ v.syms=u.syms
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraStep w16) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨(step (Or.inl rfl) ps pu ss us sp s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      exec_post (advance_ok ps ss) et,exec_post (advance_ok pu us) ev,Exec.syms et,Exec.syms ev⟩
  have trace : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (Impl.MlKem.AArch64.Paired.extraStep w16) (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraStep w16) (.block [])))
      (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.ite ?_ ?_ (RelCT.block_nil (by intros; trivial)))
    · intro t v h
      have hx : t.gpr .x6=v.gpr .x6 := BitVec.eq_of_toNat_eq (h.1.flag.trans h.2.1.flag.symm)
      change some (t.gpr .x6==0)=some (v.gpr .x6==0)
      rw [hx]
    · intro t v tr ur t' v' h et ev
      exact step (Or.inr rfl) h.1.1.progress h.1.2.1.progress
        (by rw [h.1.2.2.1]; exact ss) (by rw [h.1.2.2.2]; exact us)
        (h.1.1.keep.sp.trans (sp.trans h.1.2.1.keep.sp.symm)) t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (bounded_ok (fun _ ht hs=>advance_ok ht hs) ps ss) et,
    exec_post (bounded_ok (fun _ ht hs=>advance_ok ht hs) pu us) ev⟩

structure CleanupW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) (s : State) : Prop where
  context : Context p a b c s
  pointer : s.gpr .x19=p
  left : Rej8.Scalar.CoeffsW w16 s.mem a (accepted A 5)
  right : Rej8.Scalar.CoeffsW w16 s.mem b (accepted B 5)
  saveLeft : checkpointW w16 (p+1680) a (accepted A 5) s.mem
  saveRight : checkpointW w16 (p+1696) b (accepted B 5) s.mem

abbrev Cleanup := CleanupW false

theorem BoundedW.cleanup {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : BoundedW w16 A B p a b c s u) : CleanupW w16 A B p a b c u :=
  ⟨h.context,h.ptr,h.left,h.right,h.saveLeft,h.saveRight⟩

theorem CleanupW.only {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (h : CleanupW w16 A B p a b c s) (k : Only [.x24] s u) : CleanupW w16 A B p a b c u := by
  refine ⟨h.context.frame k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _),?_,?_,?_,?_,?_⟩
  · rw [k.get .x19]; exact h.pointer
  all_goals rw [k.mem]
  · exact h.left
  · exact h.right
  · exact h.saveLeft
  · exact h.saveRight

theorem CleanupW.zeroLeft {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : CleanupW w16 A B p a b c s) : ZeroReadyW w16 (accepted A 5) 1680 a s := by
  refine ⟨accepted_length A 5,h.left,?_,?_,?_,?_⟩
  · rw [h.pointer]; exact h.saveLeft
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · intro i hi; exact Noise.inScratch h.context.outA (cs_store_le w16 hi) (by decide)

theorem CleanupW.zeroRight {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : CleanupW w16 A B p a b c s) : ZeroReadyW w16 (accepted B 5) 1696 b s := by
  refine ⟨accepted_length B 5,h.right,?_,?_,?_,?_⟩
  · rw [h.pointer]; exact h.saveRight
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · rw [h.pointer]; exact in_rd_wr (Noise.inScratch h.context.scratch (by decide) (by decide))
  · intro i hi; exact Noise.inScratch h.context.outB (cs_store_le w16 hi) (by decide)

theorem mask_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x24 .x24 .x6]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem resume_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (step : StepTimingW w16 A B p a b c) (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraPair w16)
      (fun t v=>ResumePostW w16 A B p a b s t ∧ ResumePostW w16 A B p a b u v) := by
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraPair w16) (fun _ _=>True) := by
    change RelCT isa _ (.seq _ (.seq (.ite _ _ _) _)) _
    apply RelCT.assoc
    refine RelCT.seq (bounded_relCT step ps pu ss us sp) ?_
    refine RelCT.seq (R:=fun t v : State=>CleanupW w16 A B p a b c t ∧ CleanupW w16 A B p a b c v ∧ t.sp=v.sp) ?_ ?_
    · intro t v tr ur t' v' h et ev
      have mt : Only [.x24] t t' := (exec_post (wp_and (fun w kw ew=>wp_nil (show Only [.x24] t w from kw))) et)
      have mv : Only [.x24] v v' := (exec_post (wp_and (fun w kw ew=>wp_nil (show Only [.x24] v w from kw))) ev)
      have hv : t.sp=v.sp := h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)
      exact ⟨mask_ct t v tr ur t' v' trivial trivial (agree_of hv (by simp)) et ev,
        h.1.cleanup.only mt,h.2.cleanup.only mv,mt.sp.trans (hv.trans mv.sp.symm)⟩
    · intro t v tr ur t' v' h et ev
      exact zeroBoth_relCT h.1.zeroLeft h.1.zeroRight h.2.1.zeroLeft h.2.1.zeroRight h.1.context.apart
        (by rw [h.1.pointer]; exact h.1.context.farA.sub_left (Offset.sub_base p (by decide)))
        h.2.2 (h.1.pointer.trans h.2.1.pointer.symm) t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (extraPair_ok ps ss) et,exec_post (extraPair_ok pu us) ev⟩

end VG.Proof.MlKem.AArch64.Paired
