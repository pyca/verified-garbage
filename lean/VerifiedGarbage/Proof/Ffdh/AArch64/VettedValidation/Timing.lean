module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.RecognizeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Correct
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Spec.Rsa.Contract

/-! The fast acceptance and general fallback both depend only on the public domain. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open Cached

def Recognized (q : Public) (t : State) : Prop := ∃s,Ready q s ∧ Result s t

def RestoredReady (q : Public) (t : State) : Prop := ∃s,Ready q s ∧ Restored s t

theorem ready_width {q : Public} {s : State} (h : Ready q s) :
    width s=policyWidth 4095 q.k.toNat q.dom Policy.groups := by
  unfold width
  rw [h.keyLength,h.bytes]

theorem recognized_eval {q : Public} {t : State} (h : Recognized q t) :
    isa.eval (.nonzero .x .x10) t=some (decide (policyWidth 4095 q.k.toNat q.dom Policy.groups≠4095)) := by
  obtain ⟨s,ready,result⟩:=h
  rw [result_eval result,ready_width ready]

theorem restore_ct : RelCT isa (Two Recognized)
    (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore) (fun _ _ =>True) :=
  two_taint [.x0] (fun _ _ _ hs ht r hr =>by
    have same : r= .x0 := by simpa using hr
    subst r
    obtain ⟨s,hs,resultS⟩:=hs
    obtain ⟨t,ht,resultT⟩:=ht
    exact (resultS.base.trans hs.base).trans (resultT.base.trans ht.base).symm) (by taint_decide)

theorem restored_pub {q : Public} {s t : State} (hs : RestoredReady q s) (ht : RestoredReady q t)
    (sp : s.sp=t.sp) : CheckDomain.cdPub s t := by
  obtain ⟨a,ha,sa⟩:=hs
  obtain ⟨b,hb,tb⟩:=ht
  refine ⟨sp,?_,?_,?_,?_,?_,?_⟩
  · rw [sa.domain,ha.bytes,tb.domain,hb.bytes]
  · exact (sa.args.1.trans ha.domain).trans (tb.args.1.trans hb.domain).symm
  · exact (sa.args.2.1.trans ha.length).trans (tb.args.2.1.trans hb.length).symm
  · exact (sa.args.2.2.1.trans ha.keyLength).trans (tb.args.2.2.1.trans hb.keyLength).symm
  · exact (sa.args.2.2.2.1.trans ha.base).trans (tb.args.2.2.2.1.trans hb.base).symm
  · exact (sa.args.2.2.2.2.trans ha.words).trans (tb.args.2.2.2.2.trans hb.words).symm

theorem miss_ct (W : Window) (M : Mont) (S : Selector) : RelCT isa (Two Recognized)
    (.seq (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore)
      (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)) (fun _ _ =>True) := by
  refine RelCT.seq (two_post (Ψ:=RestoredReady) restore_ct ?_) ?_
  · intro q s h
    obtain ⟨original,ready,result⟩:=h
    exact WP.mono (restore_ok (geometry ready.assumptions) result) (fun _ restored =>⟨original,ready,restored⟩)
  · exact (fallback_ct W M S).mono (fun s t ⟨q,hs,ht,sp⟩ =>
      ⟨hs.choose_spec.2.pre hs.choose_spec.1.assumptions,
       ht.choose_spec.2.pre ht.choose_spec.1.assumptions,restored_pub hs ht sp⟩) (fun _ _ h =>h)

theorem native_ct (W : Window) (M : Mont) (S : Selector) : RelCT isa (Two Ready)
    (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) (fun _ _ =>True) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.code
  refine RelCT.seq (two_post (Ψ:=Recognized) recognize_ct (fun q s h =>
    WP.mono (recognize_ok (geometry h.assumptions)) (fun _ result =>⟨s,h,result⟩))) ?_
  refine RelCT.ite (fun s t ⟨q,hs,ht,_⟩ =>(recognized_eval hs).trans (recognized_eval ht).symm) ?_ ?_
  · exact (two_taint [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide)).mono
      (fun _ _ h =>h.1) (fun _ _ h =>h)
  · exact (miss_ct W M S).mono (fun _ _ h =>h.1) (fun _ _ h =>h)

def publicInput (s : State) (g : Geometry s) : Public :=
  ⟨s.gpr .x0,s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4,s.syms Policy.tableSym,CheckDomain.cdDom s,
    g.small,g.large,g.room,
    by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape,
    by simp only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range]⟩

theorem constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa pre pub (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) := by
  intro s t ts tt u v hs ht hp es et
  obtain ⟨⟨sp,bytes,r0,r1,r2,r3,r4⟩,symbol⟩:=hp
  have sameBytes : CheckDomain.cdDom s=CheckDomain.cdDom t := by
    have recover:=congrArg (List.map (BitVec.ofNat 8)) bytes
    simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
  let q:=publicInput s (geometry hs)
  have first : Ready q s :=⟨hs,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have second : Ready q t :=⟨ht,r0.symm,r1.symm,r2.symm,r3.symm,r4.symm,sameBytes.symm,symbol.symm⟩
  exact ((native_ct W M S) _ _ _ _ _ _ ⟨q,first,second,sp⟩ es et).1

end VG.Proof.Ffdh.AArch64.VettedValidation
