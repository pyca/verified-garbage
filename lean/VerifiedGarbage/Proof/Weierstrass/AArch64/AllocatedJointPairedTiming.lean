import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPairedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointLoop

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 Spec.Weierstrass

/-- Attach the point invariant and preserved counter to a field-level timing proof. -/
theorem allocatedJointPair_stage {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A B : Point C} {code : Prog isa} {rs : List Reg} {W : List (Nat × Nat)}
    (h19 : Reg.x19∉rs)
    (hw : ∀ s, Core A s → s.gpr .x19=BitVec.ofNat 64 j →
      WP isa code s fun t => AllocatedFrame rs base W s t ∧ Core B t)
    (ht : ∀ E,RelCT isa (fun s t =>
      FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
      Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
      code (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)) :
    RelCT isa (JointPair c C base size Core A j) code (JointPair c C base size Core B j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨he,hp'⟩ := ht E _ _ _ _ _ _ ⟨hp,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,ks,cs'⟩ := hw s cs ps
  obtain ⟨_,_,xt,kt,ct'⟩ := hw t ct pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,hp',cs',ct',(ks.regs.gpr _ h19).trans ps,
    (kt.regs.gpr _ h19).trans pt⟩

theorem allocatedJointPair_digits {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q A : Point C}
    (hC : Law C) (hQ : onCurve C Q=true) (hA : onCurve C A=true) (hj : j<257)
    (hw : AllocatedJointOpsOk c o C base rs W Core P Q u v) (ht : JointOpsTiming c o C base size Core) :
    RelCT isa (JointPair c C base size Core A j) (Joint.digits c o)
      (JointPair c C base size Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)) j) := by
  apply RelCT.seq (allocatedJointPair_stage hw.counter (fun s hs h19 => hw.peer A j s hj hA hs h19) (ht.peer A j hj))
  exact allocatedJointPair_stage hw.counter (fun s hs h19 => hw.generator _ j s hj
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) hs h19) (ht.generator _ j hj)

theorem allocatedJointPair_step {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true) (hj : j<256)
    (hw : AllocatedJointOpsOk c o C base rs W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core (jointPoint P Q u v (j+1)) (j+1))
      (Joint.step c o) (JointPair c C base size Core (jointPoint P Q u v j) j) := by
  have hA := jointPoint_curve hC hP hQ u v (j+1)
  apply RelCT.seq (jointPair_counter hw.keep hj hc)
  apply RelCT.seq (allocatedJointPair_stage hw.counter (fun s hs _ => hw.double _ s hA hs) (ht.double _ j))
  simpa only [jointPoint_step hC hP hQ] using
    allocatedJointPair_digits hC hQ (hC.onCurve_add hA hA) (by omega : j<257) hw ht

theorem allocatedJointPair_run {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v : Nat} {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (hw : AllocatedJointOpsOk c o C base rs W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core .infinity 256) (Joint.run c o)
      (JointPair c C base size Core (add (mul u P) (mul v Q)) 0) := by
  have seed := allocatedJointPair_digits (j:=256) (A:=.infinity) hC hQ rfl (by decide) hw ht
  have he := jointPoint_step hC hP hQ u v 256
  rw [jointPoint_top P Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P 7 u 256)=jointPoint P Q u v 256 at he
  rw [he] at seed
  have out := jointRun_relCT (c:=c) (o:=o)
    (fun j => JointPair c C base size Core (jointPoint P Q u v j) j)
    (fun _ _ _ h => ⟨h.2.2.2.1,h.2.2.2.2⟩) seed
    (fun j hj => allocatedJointPair_step hC hP hQ hj hw ht hc)
  simpa only [jointPoint_zero] using out

end VG.Proof.Weierstrass.AArch64
