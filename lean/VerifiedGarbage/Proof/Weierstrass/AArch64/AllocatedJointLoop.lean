module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-! ### `Weierstrass.AArch64.JointPairedTiming`, which the modules that import this one used -/

section

/-! ### `Weierstrass.AArch64.JointLoop`, which only this module used -/

section

/-! Shared doubling and two independent signed digits compose without an affine conversion. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

structure JointLoopKeep (M : Mod) (base : Addr) (W : List Nat) (s t : State) : Prop where
  regs : KeepRegs (.x19::clob M.n) s t
  unch : Unch base (W.map (·,8*M.n)++[(M.tmp,8*M.n)]) s.mem t.mem

theorem JointLoopKeep.of_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State}
    (h : ProgKeep M base W s t) : JointLoopKeep M base W s t :=
  ⟨(⟨h.gpr,h.rd,h.wr,h.sp⟩ : KeepRegs (clob M.n) s t).mono
    (fun _ hr => List.mem_cons_of_mem _ hr),h.unch⟩

end VG.Proof.Weierstrass.AArch64

end

end


@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 Spec.Weierstrass

def JointPair (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat)
    (Core : Point C → State → Prop) (A : Point C) (j : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E s t) ∧
    Core A s ∧ Core A t ∧ s.gpr .x19=BitVec.ofNat 64 j ∧ t.gpr .x19=BitVec.ofNat 64 j

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

theorem jointPair_counter {c : Joint.Cfg} {C : Curve} {base : Addr} {size j : Nat}
    {Core : Point C → State → Prop} {A : Point C}
    (hkeep : ∀ A s t,VG.Proof.Ed25519.AArch64.Keeps [.x19] s t → t.syms=s.syms → Core A s → Core A t)
    (hj : j<256)
    (hc : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x19])) (.block [decCounter])) :
    RelCT isa (JointPair c C base size Core A (j+1)) (.block [decCounter])
      (JointPair c C base size Core A j) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
  obtain ⟨_,_,xs,s19,ks⟩ := decCounter_ok s (by omega_using []) (by omega_using [hj]) ps
  obtain ⟨_,_,xt,t19,kt⟩ := decCounter_ok t (by omega_using []) (by omega_using [hj]) pt
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

end VG.Proof.Weierstrass.AArch64

end

end

/-! The joint scalar loop with an explicit internal register and byte frame.

Only the loop counter must survive its arithmetic blocks. The outer verifier
is responsible for restoring any additional ABI registers after the loop.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The loop invariant may include arbitrary stable tables and initialized cached fields. -/
structure AllocatedJointOpsOk (c : Joint.Cfg) (o : Joint.Ops) (C : Curve) (base : Addr)
    (rs : List Reg) (W : List (Nat × Nat)) (Core : Point C → State → Prop) (P Q : Point C) (u v : Nat) : Prop where
  counter : Reg.x19∉rs
  keep : ∀ A s t, Keeps [.x19] s t → t.syms=s.syms → Core A s → Core A t
  double : ∀ A s, onCurve C A=true → Core A s →
    WP isa o.double s fun t => AllocatedFrame rs base W s t ∧ Core (add A A) t
  peer : ∀ A j s, j<257 → onCurve C A=true → Core A s →
    s.gpr .x19=BitVec.ofNat 64 j → WP isa o.digitQ s fun t =>
      AllocatedFrame rs base W s t ∧ Core (add A (FastNaf.point C Q 5 v j)) t
  generator : ∀ A j s, j<257 → onCurve C A=true → Core A s →
    s.gpr .x19=BitVec.ofNat 64 j → WP isa (Joint.fixedDigit c o.mixedAdd) s fun t =>
      AllocatedFrame rs base W s t ∧ Core (add A (FastNaf.point C P c.gw u j)) t

theorem allocatedJointDigits_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v j : Nat}
    (hC : Law C) (hQ : onCurve C Q=true) (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v)
    {A : Point C} (hA : onCurve C A=true) {s : State} (hs : Core A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.digits c o) s fun t => AllocatedFrame rs base W s t ∧
      Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P c.gw u j)) t := by
  rw [Joint.digits]
  apply WP.seq
  refine WP.mono (hops.peer A j s hj hA hs h19) fun a ⟨ka,ca⟩ => ?_
  refine WP.mono (hops.generator _ j a hj
    (hC.onCurve_add hA (FastNaf.onCurve_point hC hQ 5 v j)) ca
    ((ka.regs.gpr _ hops.counter).trans h19)) fun t ⟨kt,ct⟩ => ⟨ka.trans kt,ct⟩

theorem allocatedJointStep_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v j : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v) (hj : j<256)
    {s : State} (hs : Core (jointPoint P Q u v (j+1) c.gw) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Joint.step c o) s fun t => AllocatedFrame (.x19::rs) base W s t ∧
      Core (jointPoint P Q u v j c.gw) t ∧ t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Joint.step]
  apply WP.seq
  refine WP.mono_syms (decCounter_ok s (by omega_using []) (by omega_using [hj]) h19) fun a ⟨a19,ka⟩ hsym => ?_
  have ca := hops.keep _ s a ka hsym hs
  apply WP.seq
  refine WP.mono (hops.double _ a (jointPoint_curve hC hP hQ u v (j+1) c.gw) ca) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.regs.gpr _ hops.counter,a19,Nat.add_sub_cancel]
  refine WP.mono (allocatedJointDigits_ok hC hQ hops
    (hC.onCurve_add (jointPoint_curve hC hP hQ u v (j+1) c.gw) (jointPoint_curve hC hP hQ u v (j+1) c.gw))
    cb (by omega_using [hj]) b19) fun t ⟨kt,ct⟩ => ?_
  rw [jointPoint_step hC hP hQ (gw:=c.gw)] at ct
  have kp := kb.trans kt
  refine ⟨⟨(Keeps.regs ka).mono (by simp) |>.trans
    (kp.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr)),?_⟩,ct,?_⟩
  · simpa only [ka.mem] using kp.unch
  · rw [kt.regs.gpr _ hops.counter,b19]

theorem allocatedJointLoop_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v)
    {s : State} (hs : Core (jointPoint P Q u v 256 c.gw) s) (h19 : s.gpr .x19=256) :
    WP isa (.loop (Joint.step c o) (.nonzero .x .x19)) s fun t =>
      AllocatedFrame (.x19::rs) base W s t ∧ Core (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  let I := fun j t => AllocatedFrame (.x19::rs) base W s t ∧
    Core (jointPoint P Q u v j c.gw) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv:=I) (n:=256) (by decide)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have he : j-1+1=j := by omega_using [hj1]
    refine WP.mono (allocatedJointStep_ok hC hP hQ hops (by omega_using [hj256]) (he.symm ▸ ca) (he.symm ▸ a19))
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    rw [jointPoint_zero (gw:=c.gw)] at ct
    exact ⟨kt,ct,t19⟩
  · decide
  · exact ⟨AllocatedFrame.refl _ _ _ _,hs,h19⟩

/-- Seed the possible carry digit, then consume all 256 remaining positions. -/
theorem allocatedJointRun_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v) (hu : u<2^256) (hv : v<2^256)
    {s : State} (hs : Core .infinity s) (h19 : s.gpr .x19=256) :
    WP isa (Joint.run c o) s fun t => AllocatedFrame (.x19::rs) base W s t ∧
      Core (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  rw [Joint.run]
  apply WP.seq
  refine WP.mono (allocatedJointDigits_ok hC hQ hops (A:=.infinity) rfl hs (by decide) h19)
    fun a ⟨ka,ca⟩ => ?_
  have he := jointPoint_step hC hP hQ u v 256 c.gw
  rw [jointPoint_top P Q hu hv c.gw] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P c.gw u 256)=jointPoint P Q u v 256 c.gw at he
  rw [he] at ca
  refine WP.mono (allocatedJointLoop_ok hC hP hQ hops ca
    ((ka.regs.gpr _ hops.counter).trans h19)) fun t ⟨kt,ct,t19⟩ =>
      ⟨(ka.widenRegs (fun _ hr => List.mem_cons_of_mem _ hr)).trans kt,ct,t19⟩

end VG.Proof.Weierstrass.AArch64
