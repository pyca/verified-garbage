module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem bothStart_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothNext_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [.logic .and .x .x22 .x22 .x0,.addImm .x .x20 .x20 504,.addImm .x .x1 .x1 16,
      .subImm .x .x23 .x23 1]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem bothEnd_ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
    (.block [Impl.MlKem.AArch64.mov .x6 .x22]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

/-- An iteration of `extraBoth` from a stream ready at the same place in both runs. -/
theorem bothBody_relCT {w16 : Bool} {t v : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (pt : ReadyW w16 L B (t.gpr .x20) (t.gpr .x1) aP t) (pv : ReadyW w16 L B (v.gpr .x20) (v.gpr .x1) aP v)
    (ct : Rej8.Constants t) (cv : Rej8.Constants v) (sp : t.sp=v.sp) (h20 : t.gpr .x20=v.gpr .x20)
    (h1 : t.gpr .x1=v.gpr .x1) (h16 : t.gpr .x16=v.gpr .x16) :
    RelCT isa (fun x y=>x=t ∧ y=v) (bothBody w16) (fun _ _=>True) := by
  refine RelCT.seq (R:=fun x y : State=>x.sp=y.sp) ?_ ?_
  · intro x y tx ty x' y' h ex ey
    have r := extra_relCT pt pv ct cv sp h20 h1 h16 x y tx ty x' y' h ex ey
    exact ⟨r.1,r.2.1.keep.sp.trans (sp.trans r.2.2.keep.sp.symm)⟩
  · intro x y tx ty x' y' h ex ey
    exact ⟨bothNext_ct x y tx ty x' y' trivial trivial (agree_of h (by simp)) ex ey,trivial⟩

theorem extraBoth_relCT {w16 : Bool} {s u : State} {L M : List Zq} {A B : Nat→Byte} {p a b : Addr}
    (hs : BothReadyW w16 L M A B p a b s) (hu : BothReadyW w16 L M A B p a b u)
    (sp : s.sp=u.sp) (table : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun x y=>x=s ∧ y=u) (Impl.MlKem.AArch64.Paired.extraBoth w16) (fun _ _=>True) := by
  let I : Nat → State → State → Prop := fun n t v =>
    (n=2 ∧ BothInv w16 L M A B p a b s 0 t ∧ BothInv w16 L M A B p a b u 0 v) ∨
    (n=1 ∧ BothInv w16 L M A B p a b s 1 t ∧ BothInv w16 L M A B p a b u 1 v)
  have start : RelCT isa (fun x y=>x=s ∧ y=u)
      (.block [.addImm .x .x20 .x19 400,.addImm .x .x1 .x19 1680,.movz .x .x22 1 0,.movz .x .x23 2 0]) (I 2) := by
    intro x y tx ty x' y' h ex ey
    rcases h with ⟨rfl,rfl⟩
    exact ⟨bothStart_ct x y tx ty x' y' trivial trivial (agree_of sp (by simp)) ex ey,
      .inl ⟨rfl,exec_post (bothStart_ok hs) ex,exec_post (bothStart_ok hu) ey⟩⟩
  have loop : RelCT isa (I 2) (.loop (bothBody w16) (.nonzero .x .x23)) (fun t v=>t.sp=v.sp) := by
    refine RelCT.loop (M:=isa) I (fun n => ?_) 2
    intro t v tt tv t' v' hI et ev
    rcases hI with ⟨rfl,it,iv⟩|⟨rfl,it,iv⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,ra,_⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,rb,_⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact ra) (by rw [v20,v1]; exact rb) ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep0_ok hs it) et).1
      have iv' := (exec_post (bothStep0_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some true := by rw [eval_nonzero,it'.2.2.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some true := by rw [eval_nonzero,iv'.2.2.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun h => (by rw [et23] at h; cases h),fun _ => ⟨1,by decide,.inr ⟨rfl,it',iv'⟩⟩⟩
    · obtain ⟨kt,_,ct,t20,t1,_,_,_,_,rb⟩ := id it
      obtain ⟨kv,_,cv,v20,v1,_,_,_,_,rb'⟩ := id iv
      have tq := bothBody_relCT (by rw [t20,t1]; exact rb) (by rw [v20,v1]; exact rb') ct cv
        (kt.sp.trans (sp.trans kv.sp.symm)) (t20.trans v20.symm) (t1.trans v1.symm)
        (by rw [kt.get .x16,kv.get .x16,table]) t v tt tv t' v' ⟨rfl,rfl⟩ et ev
      have it' := (exec_post (bothStep1_ok hs it) et).1
      have iv' := (exec_post (bothStep1_ok hu iv) ev).1
      have et23 : isa.eval (.nonzero .x .x23) t'=some false := by rw [eval_nonzero,it'.2.2.2.1]; rfl
      have ev23 : isa.eval (.nonzero .x .x23) v'=some false := by rw [eval_nonzero,iv'.2.2.2.1]; rfl
      refine ⟨tq.1,by rw [et23,ev23],fun _ => it'.1.sp.trans (sp.trans iv'.1.sp.symm),
        fun h => by rw [et23] at h; cases h⟩
  refine RelCT.seq start (RelCT.seq loop ?_)
  intro t v tt tv t' v' h et ev
  exact ⟨bothEnd_ct t v tt tv t' v' trivial trivial (agree_of h (by simp)) et ev,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
