import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 Spec.Weierstrass

def JointPair (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Core : Point C → State → Prop) (A : Point C) (j : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t) ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

/-- Attach the point invariant and preserved counter to a field-level timing proof. -/
theorem jointPair_stage {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A B : Point C} {code : Prog isa} {W : List Nat}
    (hw : ∀ s, Core A s → s.gpr .x19=BitVec.ofNat 64 j →
      WP isa code s fun t => ProgKeep c.K.M base W s t ∧ Core B t)
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
  exact ⟨he,hp',cs',ct',(ks.gpr _ (x19_not_clob _)).trans ps,
    (kt.gpr _ (x19_not_clob _)).trans pt⟩

structure JointOpsTiming (c : Joint.Cfg) (o : Joint.Ops) (C : Curve) (base : Addr)
    (size : Nat) (Core : Point C → State → Prop) : Prop where
  double : ∀ A j E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    o.double (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  peer : ∀ A j,j<257 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    o.digitQ (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)
  generator : ∀ A j,j<257 → ∀ E,RelCT isa (fun s t =>
    FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j)
    (Joint.fixedDigit c o.mixedAdd)
    (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t)

theorem jointPair_digits {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q A : Point C}
    (hC : Law C) (hQ : onCurve C Q=true) (hA : onCurve C A=true) (hj : j<257)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core) :
    RelCT isa (JointPair c C base size Core A j) (Joint.digits c o)
      (JointPair c C base size Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)) j) := by
  apply RelCT.seq (jointPair_stage (fun s hs h19 => hw.peer A j s hj hA hs h19) (ht.peer A j hj))
  exact jointPair_stage (fun s hs h19 => hw.generator _ j s hj
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) hs h19) (ht.generator _ j hj)

theorem jointPair_counter {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,VG.Proof.Ed25519.AArch64.Keeps [.x19] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j<256)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core A (j+1)) (.block [decCounter])
      (JointPair c C base size Core A j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,s19,ks⟩ := decCounter_ok s (by omega) (by omega) ps
  obtain ⟨_,_,xt,t19,kt⟩ := decCounter_ok t (by omega) (by omega) pt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have he : ts=tt := hc _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
    subst hr
    exact ps.trans pt.symm⟩ es et
  refine ⟨he,⟨E,hp.left.of_keeps ks (by decide),hp.right.of_keeps kt (by decide),
    ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,hkeep A _ _ ks (Exec.syms es) cs,hkeep A _ _ kt (Exec.syms et) ct,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using s19
  · simpa only [Nat.add_sub_cancel] using t19

theorem jointPair_step {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v j : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true) (hj : j<256)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core (jointPoint P Q u v (j+1)) (j+1))
      (Joint.step c o) (JointPair c C base size Core (jointPoint P Q u v j) j) := by
  have hA := jointPoint_curve hC hP hQ u v (j+1)
  apply RelCT.seq (jointPair_counter hw.keep hj hc)
  apply RelCT.seq (jointPair_stage (fun s hs _ => hw.double _ s hA hs) (ht.double _ j))
  simpa only [jointPoint_step hC hP hQ] using
    jointPair_digits hC hQ (hC.onCurve_add hA hA) (by omega : j<257) hw ht

theorem jointPair_run {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {size u v : Nat} {W : List Nat} {Core : Point C → State → Prop} {P Q : Point C}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256)
    (hw : JointOpsOk c o C base W Core P Q u v) (ht : JointOpsTiming c o C base size Core)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core .infinity 256) (Joint.run c o)
      (JointPair c C base size Core (add (mul u P) (mul v Q)) 0) := by
  have seed := jointPair_digits (j:=256) (A:=.infinity) hC hQ rfl (by decide) hw ht
  have he := jointPoint_step hC hP hQ u v 256
  rw [jointPoint_top P Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P 7 u 256)=jointPoint P Q u v 256 at he
  rw [he] at seed
  have out := jointRun_relCT (c:=c) (o:=o)
    (fun j => JointPair c C base size Core (jointPoint P Q u v j) j)
    (fun _ _ _ h => ⟨h.2.2.2.1,h.2.2.2.2⟩) seed
    (fun j hj => jointPair_step hC hP hQ hj hw ht hc)
  simpa only [jointPoint_zero] using out

end VG.Proof.Weierstrass.AArch64
