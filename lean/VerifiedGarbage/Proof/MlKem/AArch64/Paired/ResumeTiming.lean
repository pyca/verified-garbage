module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroTiming

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraPair
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
/-! # Fourth/fifth-block continuation branches only on the public matrix streams -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/ZeroBothTiming.lean`, which only this module imported.
section

/-! # The paired failure cleanup depends only on the public accepted lengths -/
section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem ZeroReadyW.frame {w16 : Bool} {s u : State} {L : List Zq} {p : Addr} {slot : Nat} {rs : List Region}
    (h : ZeroReadyW w16 L slot p s) (hr : u.rd=s.rd) (hw : u.wr=s.wr) (hx : u.gpr .x19=s.gpr .x19)
    (hf : Frame rs s.mem u.mem) (hd : ∀r∈rs,(polyRegion p).Disjoint r)
    (hc : ∀r∈rs,(Region.mk (s.gpr .x19+BitVec.ofNat 64 slot) 16).Disjoint r) : ZeroReadyW w16 L slot p u := by
  refine ⟨h.len,coeffs_frame h.coeffs h.len hf hd,?_,?_,?_,?_⟩
  · rw [hx]; exact checkpoint_frame h.saved hf hc
  · simpa only [hr,hw,hx] using h.read0
  · simpa only [hr,hw,hx] using h.read1
  · simpa only [hw] using h.writable

theorem zeroBoth_relCT {w16 : Bool} {s u : State} {a b : Addr} {L M : List Zq}
    (sa : ZeroReadyW w16 L 1680 a s) (sb : ZeroReadyW w16 M 1696 b s)
    (ua : ZeroReadyW w16 L 1680 a u) (ub : ZeroReadyW w16 M 1696 b u)
    (hab : (polyRegion a).Disjoint (polyRegion b))
    (hcp : (Region.mk (s.gpr .x19+1696) 16).Disjoint (polyRegion a))
    (hsp : s.sp=u.sp) (hx : s.gpr .x19=u.gpr .x19) :
    RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680 w16) (Impl.MlKem.AArch64.Paired.zeroExtra 1696 w16))
      (fun _ _=>True) := by
  let R := fun t v : State=>ZeroReadyW w16 M 1696 b t ∧ ZeroReadyW w16 M 1696 b v ∧
    t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19
  refine RelCT.seq (R:=R) ?_ ?_
  · intro t v tr ur t' v' h et ev
    rcases h with ⟨ht0,hv0⟩
    subst t; subst v
    have ht := exec_post (zeroExtra_ok s (by decide) (by decide) sa.len sa.coeffs sa.saved sa.read0 sa.read1 sa.writable) et
    have hu := exec_post (zeroExtra_ok u (by decide) (by decide) ua.len ua.coeffs ua.saved ua.read0 ua.read1 ua.writable) ev
    refine ⟨(zeroExtra_relCT (by decide) (by decide) sa ua hsp hx s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      sb.frame ht.1.rd ht.1.wr (ht.1.get .x19) ht.2.1 ?_ ?_,
      ub.frame hu.1.rd hu.1.wr (hu.1.get .x19) hu.2.1 ?_ ?_,
      ht.1.sp.trans (hsp.trans hu.1.sp.symm),?_⟩
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hcp
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr,←hx]; exact hcp
    · rw [ht.1.get .x19,hu.1.get .x19,hx]
  · intro t v tr ur t' v' h et ev
    exact ⟨(zeroExtra_relCT (by decide) (by decide) h.1 h.2.1 h.2.2.1 h.2.2.2
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev).1,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def StepTimingW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) : Prop :=
  ∀{s u : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c s → ProgressW w16 A B n p a b c u →
    s.syms "VG_MLKEM_REJ_SHUFFLE"=c → u.syms "VG_MLKEM_REJ_SHUFFLE"=c → s.sp=u.sp →
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.extraStep w16) (fun _ _=>True)

abbrev StepTiming := StepTimingW false

theorem retryInit_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.movz .x .x30 1 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem retryCond_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.sub .x .x7 .x6 .x30,.lsr .x .x7 .x7 63,.movz .x .x30 0 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `Paired.retry` from the same count in both runs. -/
theorem retryBody_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u t v : State} {n : Nat}
    (step : StepTimingW w16 A B p a b c) (it : RetryInv w16 A B p a b c s n t)
    (iv : RetryInv w16 A B p a b c u n v) (sp : t.sp=v.sp) :
    RelCT isa (fun t' v'=>t'=t ∧ v'=v) (.seq (Impl.MlKem.AArch64.Paired.extraStep w16)
      (.block [.sub .x .x7 .x6 .x30,.lsr .x .x7 .x7 63,.movz .x .x30 0 0])) (fun _ _=>True) := by
  refine RelCT.seq (R:=fun t' v' : State=>t'.sp=v'.sp) ?_ ?_
  · intro t₀ v₀ tr ur t' v' h et ev
    rcases h with ⟨rfl,rfl⟩
    have n34 : 4-n=3 ∨ 4-n=4 := by have := it.le; omega
    exact ⟨(step n34 it.progress iv.progress it.syms iv.syms sp t₀ v₀ tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      (exec_post (advance_ok it.progress it.syms) et).keep.sp.trans
        (sp.trans (exec_post (advance_ok iv.progress iv.syms) ev).keep.sp.symm)⟩
  · intro t₀ v₀ tr ur t' v' h et ev
    exact ⟨retryCond_ct t₀ v₀ tr ur t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

theorem bounded_relCT {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s u : State}
    (step : StepTimingW w16 A B p a b c) (ps : ProgressW w16 A B 3 p a b c s) (pu : ProgressW w16 A B 3 p a b c u)
    (ss : s.syms "VG_MLKEM_REJ_SHUFFLE"=c) (us : u.syms "VG_MLKEM_REJ_SHUFFLE"=c) (sp : s.sp=u.sp) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.retry w16)
      (fun t v=>BoundedW w16 A B p a b c s t ∧ BoundedW w16 A B p a b c u v) := by
  let I := fun n t v=>RetryInv w16 A B p a b c s n t ∧ RetryInv w16 A B p a b c u n v
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.retry w16) (fun _ _=>True) := by
    refine RelCT.seq (R:=I 1) ?_ (RelCT.loop (M:=isa) (Q:=fun _ _=>True) I (fun n => ?_) 1)
    · intro t v tr ur t' v' h et ev
      rcases h with ⟨rfl,rfl⟩
      exact ⟨retryInit_ct t v tr ur t' v' trivial trivial (agree_of sp (by simp)) et ev,
        exec_post (retryInit_ok ps ss) et,exec_post (retryInit_ok pu us) ev⟩
    · intro t v tr ur t' v' h et ev
      rcases h with ⟨it,iv⟩
      have sp' : t.sp=v.sp := it.keep.sp.trans (sp.trans iv.keep.sp.symm)
      have tq := (retryBody_relCT step it iv sp' t v tr ur t' v' ⟨rfl,rfl⟩ et ev).1
      obtain ⟨et',-,it'⟩ := exec_post (retryStep_ok (fun _ ht hs=>advance_ok ht hs) it) et
      obtain ⟨ev',-,iv'⟩ := exec_post (retryStep_ok (fun _ ht hs=>advance_ok ht hs) iv) ev
      refine ⟨tq,by rw [et',ev'],fun _=>trivial,fun h=>?_⟩
      have hr : retryAgain A B n=true := by rw [et'] at h; exact Option.some.inj h
      have hn : n=1 := by simp only [retryAgain,decide_eq_true_eq] at hr; exact hr.1
      exact ⟨0,by omega,it' hr,iv' hr⟩
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
    change RelCT isa _ (.seq (Impl.MlKem.AArch64.Paired.retry w16) (.seq (.block _) _)) _
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
