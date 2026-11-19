module

import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JointGenerator
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-! ### `Weierstrass.AArch64.AllocatedJointLoop`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Ecdsa.Verify.AArch64.JointCacheTiming`, which only this module used -/

section

/-! ## `JointBoundaryChecks` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64.P256Joint
open VG.Proof.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64

theorem jointTail_ct : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256) := by
  jac_field_ct

theorem jointFinish_ct : FieldCT (Jacobian.jacFinish cfg.K) := by
  jac_field_ct

theorem jointInit_ct : FieldCT (.block (Jacobian.infinity cfg.K cfg.K.R ++ ([.movz .x .x19 256 0] : List Instr))) := by
  jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCacheTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint Spec.Weierstrass

/-- The cached table and two public recodings, before initializing the accumulator. -/
def JointCachePair (C : Curve) (base T : Addr) (P Q : Point C) (u v : Nat) (s t : State) : Prop :=
  (∃ E,FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E s t) ∧
  JointStable cfg C base Q u v s ∧ JointStable cfg C base Q u v t ∧
  JointGenerator cfg C base 8192 P T s ∧ JointGenerator cfg C base 8192 P T t

end VG.Proof.Ecdsa.Verify.AArch64

end

end

end

/-! ### `Ecdsa.Verify.AArch64.AllocatedMixed`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

/-- Complete mixed addition preserves the infinity, doubling and opposite branches. -/
theorem mixedAdd_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base 8192 C.p Sl V E s) (hV : ∀ x∈rcbR K.S K.R K.E,x∈V)
    {P Q : Point C} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hJP : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P)
    (hJQ : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q) (hAff : E K.E.z=1) :
    WP isa VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd s
      (PointPost base V K.D (add P Q) s) := by
  let hL := JointLayout.layout.lay
  let hAl := JointLayout.layout.aligned
  have hA := apart
  have hSl : ∀ x∈rcbW K.S K.D++rcbR K.S K.R K.E,Sl x := by decide +kernel
  have hsize : 8192≤8192 := Nat.le_refl _
  rw [VG.Impl.Ecdsa.Verify.AArch64.P256Allocated.mixedAdd]
  apply fieldBranch_ok hL hAl hm hI (hV K.R.z (by simp [rcbR]))
  · intro a ia ka hz
    have hp := (hJP.z_zero_iff hC).mp hz
    rw [hp]
    exact WP.mono (copyPointJ_ok hL hAl hA hSl ia hV hJQ)
      (fun t ht => PointPost.of_jac (ht.prefix (ka.mono (by simp))))
  · intro a ia ka hpz
    have hqz : E K.E.z ≠ 0 := by rw [hAff]; exact hC.one_ne_zero
    apply WP.seq
    refine WP.mono (jacMixedInit_ok hL hAl hSl ia hV) fun b ⟨kb,ib⟩ => ?_
    apply WP.seq
    refine WP.mono (mixedHead_ok raw ib hV) fun c ⟨kc,ic,eh,er⟩ => ?_
    let EH := runOps (jacMixedHead K.S K.R K.E) (jacMixedInit K.S K.R E)
    have hkeep := (liftProg ka (by simp)).trans ((liftProg kb (by decide +kernel)).trans kc)
    have hpkeep : ∀ x ∈ rcbR K.S K.R K.E, EH x = E x := fun x hx => jacMixedHead_readonly hA E hx
    have jp : InvJ C (EH K.R.x) (EH K.R.y) (EH K.R.z) P := by
      rw [hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR]),hpkeep _ (by simp [rcbR])]
      exact hJP
    have oldV : ∀ x ∈ V, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => (mem_validAfter _ _).mpr (Or.inl (by simp [hx]))
    have hv : ∀ x ∈ rcbR K.S K.R K.R, x ∈ validAfter (jacMixedHead K.S K.R K.E) (K.S.t4::K.S.t2::V) :=
      fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
    apply fieldBranch_ok hL hAl hm ic (a := K.S.t3) (by
      rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
    · intro d id kd hz
      have hx : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using eh.symm.trans hz
      apply fieldBranch_ok hL hAl hm id (a := K.S.t5) (by
        rw [mem_validAfter]; right; simp [jacMixedHead,FOp.out])
      · intro e ie ke hrz
        have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)=0 := by simpa only [hAff,Lean.Grind.Semiring.mul_one] using er.symm.trans hrz
        have hpq := hJP.same hC hJQ hpz hqz hx hy
        have hdA : RcbApart K.S K.R K.R K.D := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
        have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hSl x (List.mem_append_left _ hx)
          · exact hSl x (List.mem_append_right _ (rcbR_self_mem _ _ _ hx))
        rw [←hpq]
        refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl (callOf_small (by decide)) hm hC ha hdA hdSl ie hv hP jp) fun t ⟨kt,it,jt⟩ => ?_
        exact (PointPost.sub ⟨_,liftProg kt (by decide +kernel),it,jt⟩ oldV).prefix
          (hkeep.trans ((liftProg kd (by simp)).trans (liftProg ke (by simp))))
      · intro e ie ke hrz
        have hy : E K.E.y*E K.R.z*(E K.R.z*E K.R.z)-E K.R.y*E K.E.z*(E K.E.z*E K.E.z)≠0 := by
          intro he
          apply hrz
          rw [er]
          simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
        have hadd := hJP.opposite hC hP hQ hJQ hpz hqz hx hy
        rw [hadd]
        refine WP.mono (infinityPoint_ok (K:=K) (o:=K.D) hL hAl
          (fun x hx => hSl x (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl <;> simp [rcbW])) ie hOne) fun t ht => ?_
        exact ((PointPost.of_jac ht).sub oldV).prefix
          (hkeep.trans ((liftProg kd (by simp)).trans (liftProg ke (by simp))))
    · intro d id kd hz
      have hh : E K.E.x*(E K.R.z*E K.R.z)-E K.R.x*(E K.E.z*E K.E.z)≠0 := by
        intro he
        apply hz
        rw [eh]
        simpa only [hAff,Lean.Grind.Semiring.mul_one] using he
      refine WP.mono (mixedTail_ok raw id hV) fun t ⟨kt,it,ht⟩ => ?_
      have jt := hJP.add_ne hC ha hP hQ hJQ hpz hqz hh
      dsimp only at jt
      rw [hAff,←ht] at jt
      exact PointPost.prefix ⟨_,kt,it,jt⟩ (hkeep.trans (liftProg kd (by simp)))


end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

end


/-! ## `JointWindow` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

abbrev cfg := P256Joint.cfg

/-- The public generator table is outside the scratch region. -/
theorem jointExternal_frame {C : Curve} {base T : Addr} {G : Point C} :
    CachedField.ExternalFrame base (JointGenerator cfg C base 8192 G T) := by
  intro s t hk hsym hs
  exact hs.keep hk hsym (by decide +kernel) (by decide)

theorem jointInitCounter_ok (s : State) :
    WP isa (.block [.movz .x .x19 256 0]) s fun t =>
      t.gpr .x19=256 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,RegUpd.gpr_write,
    Size.bits,show 16*0<64 by decide,ite_true,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,⟨fun r hr => by
    have h : r≠.x19 := by simpa using hr
    simp only [RegUpd.gpr_write,h,ite_false],rfl,rfl,rfl,rfl⟩⟩

/-- Initialize the shared accumulator after both digit strings and tables are ready. -/
theorem jointInit_ok {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hOne : cfg.K.one<C.p) {s : State}
    (hi : Inv cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) (tmv C cfg.K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s) (hg : JointGenerator cfg C base 8192 P T s) :
    WP isa (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr))) s fun t =>
      JointLoopKeep cfg.K.M base (jointWork cfg) s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T) .infinity t ∧
      t.gpr .x19=256 := by
  rw [WP.block_append_iff]
  refine WP.mono_syms (infinityPoint_ok (K:=cfg.K) (o:=cfg.K.R)
    JointLayout.layout.lay JointLayout.layout.aligned (by decide +kernel) hi hOne)
    fun a ⟨E,ka,ia,ja⟩ sy => ?_
  have kp : ProgKeep cfg.K.M base (jointWork cfg) s a := ka.mono (by decide +kernel)
  have il := ia.sub (fun _ hx => List.mem_append_right _ hx)
  have st := hs.keep kp (fun r hr => by
    have := JointLayout.layout.stableBounds r hr
    have := hi.scr.nowrap
    omega_arith) JointLayout.layout.stableSep
  have ca : JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T) .infinity a :=
    ⟨il.to_tmv,st,jointExternal_frame kp sy hg,il.point_tmv (jointLive_R cfg) ja⟩
  refine WP.mono_syms (jointInitCounter_ok a) fun t ⟨t19,kt⟩ sy' => ?_
  have ct := ca.of_keeps kt (by decide) (show JointGenerator cfg C base 8192 P T t from
    { symbol := by rw [sy']; exact ca.external.symbol
      read := by simpa only [kt.rd,kt.wr] using ca.external.read
      outside := ca.external.outside
      bounds := by simpa only [kt.mem] using ca.external.bounds
      point := by simpa only [kt.mem] using ca.external.point })
  exact ⟨⟨(JointLoopKeep.of_prog kp).regs.trans ((Keeps.regs kt).mono (by simp)),
    by simpa only [kt.mem] using kp.unch⟩,ct,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedWindow` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 Spec.Weierstrass

/-- A read-only generator outside scratch survives the allocator's spills. -/
def ExternalFrame (base : Addr) (External : State → Prop) : Prop :=
  ∀ {s t},Frame base work s t → t.syms=s.syms → External s → External t

theorem external_frame {base T : Addr} {P : Point C} :
    ExternalFrame base (JointGenerator cfg C base 8192 P T) :=
  fun hk hsym hs => hs.allocatedKeep hk hsym work_bounds

theorem cachedSum_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {u v : Nat} {Q A B : Point C} {External : State → Prop}
    (hExt : ExternalFrame base External) (hA : onCurve C A=true) (hB : onCurve C B=true) {s : State}
    (h : JointCore cfg C base 8192 Q u v External A s)
    (hi : Inv K.M base 8192 C.p Sl (CachedField.entryLive (jointLive cfg)) (tmv C K.M.n base s) s)
    (hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B)
    (h2 : tmv C K.M.n base s 5400=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)
    (h3 : tmv C K.M.n base s 5432=tmv C K.M.n base s K.E.z*(tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z)) :
    WP isa (.seq (CachedJac.add K P256Allocated.cachedOps) (.block (copyPt 4 K.R K.D))) s fun t =>
      Frame base work s t ∧ JointCore cfg C base 8192 Q u v External (add A B) t := by
  apply WP.of_syms
  apply WP.seq
  refine WP.mono (cachedAdd_ok raw hC ha hm hOne hi (by decide +kernel) h2 h3 hA hB h.point hj)
    fun b ⟨eb,kb,ib,jb⟩ => ?_
  refine WP.mono (copyPoint_ok JointLayout.layout.lay JointLayout.layout.aligned
    JointLayout.fixedLayout.copyApart (by decide +kernel) ib (by decide +kernel))
    fun t ⟨et,kt,it,hv⟩ sy => ?_
  have kp := kb.trans (liftProg kt (by decide +kernel))
  refine ⟨kp,h.allocatedNext JointLayout.layout kp work_stable
    (it.sub (fun x hx => by simp [CachedField.entryLive,hx])) ?_ (hExt kp sy h.external)⟩
  simp only [Prod.mk.injEq] at hv
  change et 512=eb 608 ∧ et 544=eb 640 ∧ et 576=eb 672 at hv
  change InvJ C (et 512) (et 544) (et 576) (add A B)
  rw [hv.1,hv.2.1,hv.2.2]
  exact jb

theorem mixedSum_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base : Addr} {u v : Nat} {Q A B : Point C} {External : State → Prop}
    (hExt : ExternalFrame base External) (hA : onCurve C A=true) (hB : onCurve C B=true) {s : State}
    (h : JointCore cfg C base 8192 Q u v External A s)
    (hi : Inv K.M base 8192 C.p Sl ([K.E.x,K.E.y,K.E.z]++jointLive cfg) (tmv C K.M.n base s) s)
    (hj : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B)
    (hz : tmv C K.M.n base s K.E.z=1) :
    WP isa (.seq P256Allocated.mixedAdd (.block (copyPt 4 K.R K.D))) s fun t =>
      Frame base work s t ∧ JointCore cfg C base 8192 Q u v External (add A B) t := by
  apply WP.of_syms
  apply WP.seq
  refine WP.mono (mixedAdd_ok raw hC ha hm hOne hi (by decide +kernel) hA hB h.point hj hz)
    fun b ⟨eb,kb,ib,jb⟩ => ?_
  refine WP.mono (copyPoint_ok JointLayout.layout.lay JointLayout.layout.aligned
    JointLayout.fixedLayout.copyApart (by decide +kernel) ib (by decide +kernel))
    fun t ⟨et,kt,it,hv⟩ sy => ?_
  have kp := kb.trans (liftProg kt (by decide +kernel))
  refine ⟨kp,h.allocatedNext JointLayout.layout kp work_stable
    (it.sub (fun x hx => by simp [hx])) ?_ (hExt kp sy h.external)⟩
  simp only [Prod.mk.injEq] at hv
  change et 512=eb 608 ∧ et 544=eb 640 ∧ et 576=eb 672 at hv
  change InvJ C (et 512) (et 544) (et 576) (add A B)
  rw [hv.1,hv.2.1,hv.2.2]
  exact jb

theorem ops_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base T : Addr} {P Q : Point C} {u v : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true) :
    AllocatedJointOpsOk cfg P256Allocated.ops C base allocatedRegs work
      (JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)) P Q u v where
  counter := allocatedRegs_x19
  keep := by
    intro A s t hk hsym hs
    apply hs.of_keeps hk (by decide)
    exact { symbol := by rw [hsym]; exact hs.external.symbol
            read := by simpa only [hk.rd,hk.wr] using hs.external.read
            outside := hs.external.outside
            bounds := by simpa only [hk.mem] using hs.external.bounds
            point := by simpa only [hk.mem] using hs.external.point }
  double := by
    intro A s hA hs
    refine WP.mono_syms (double_ok hC ha hs.field hA hs.point) fun t ⟨hk,hi,hj⟩ hsym => ?_
    exact ⟨hk,hs.allocatedNext JointLayout.layout hk work_stable hi hj
      (external_frame hk hsym hs.external)⟩
  peer := by
    intro A j s hj hA hs h19
    exact CachedField.allocatedCachedDigit_ok JointLayout.layout (by decide) hm hC
      clob4_allocatedRegs work_cover hj hQ hA jointExternal_frame
      (by intro A B s hA hB hs hi hj h2 h3
          exact cachedSum_ok raw hC ha hm hOne external_frame hA hB hs hi hj h2 h3) hs h19
  generator := by
    intro A j s hj hA hs h19
    exact allocatedJointFixedDigit_ok JointLayout.fixedLayout hm hC clob4_allocatedRegs work_cover hP hA
      (by intro A B s hA hB hs hi hj hz
          exact mixedSum_ok raw hC ha hm hOne external_frame hA hB hs hi hj hz) hs hj h19

theorem initializedRun_ok (raw : RawCorrect) (hC : Law C) (ha : AM3 C)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hOne : K.one<C.p)
    {base T : Addr} {P Q : Point C} {u v : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hu : u<2^256) (hv : v<2^256) {s : State}
    (hi : Inv K.M base 8192 C.p Sl (jointLive cfg) (tmv C K.M.n base s) s)
    (hs : JointStable cfg C base Q u v s) (hg : JointGenerator cfg C base 8192 P T s) :
    WP isa (.seq (.block (Jacobian.infinity K K.R++([.movz .x .x19 256 0] : List Instr)))
      (Joint.run cfg P256Allocated.ops)) s fun t =>
      AllocatedFrame (.x19::allocatedRegs) base work s t ∧
      JointCore cfg C base 8192 Q u v (JointGenerator cfg C base 8192 P T)
        (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  apply WP.seq
  refine WP.mono (jointInit_ok hOne hi hs hg) fun a ⟨ka,ca,a19⟩ => ?_
  have k' : AllocatedFrame (.x19::allocatedRegs) base work s a :=
    ⟨ka.regs.mono (fun r hr => (List.mem_cons.mp hr).elim (fun h => List.mem_cons.mpr (Or.inl h))
      (fun h => List.mem_cons_of_mem _ (clob4_allocatedRegs r h))),ka.unch.cover work_cover⟩
  refine WP.mono (allocatedJointRun_ok hC hP hQ (ops_ok raw hC ha hm hOne hP hQ) hu hv ca a19)
    fun t ⟨kt,ct,t19⟩ => ⟨k'.trans kt,ct,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `JointInitTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.P256Joint Spec.Weierstrass

private theorem jointInit_fields {C : Curve} {base : Addr} {E : Nat → Fe C}
    (hOne : cfg.K.one<C.p) :
    RelCT isa (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg) E)
      (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
      (FieldPair cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg)
        (infinityEnv cfg.K.M C.p cfg.K.one E cfg.K.R)) := by
  apply fieldWP_relCT jointInit_ct
  intro s hi
  have hR := wordsVal_lt s.mem base cfg.K.M.mo cfg.K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have slots : ∀ x∈[cfg.K.R.x,cfg.K.R.y,cfg.K.R.z],x∈jointSlots cfg := by decide +kernel
  rw [WP.block_append_iff]
  have iw : WP isa (.block (Jacobian.infinity cfg.K cfg.K.R)) s fun t =>
      Inv cfg.K.M base 8192 C.p (·∈jointSlots cfg) (jointLive cfg)
        (infinityEnv cfg.K.M C.p cfg.K.one E cfg.K.R) t ∧ t.sp=s.sp := by
    rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned hi
      (slots _ (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned ia
      (slots _ (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
    refine WP.mono (setField_ok JointLayout.layout.lay JointLayout.layout.aligned ib
      (slots _ (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
    exact ⟨it.sub (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hx))),kt.sp.trans (kb.sp.trans ka.sp)⟩
  refine WP.mono iw fun a ⟨ia,sp⟩ => ?_
  refine WP.mono (jointInitCounter_ok a) fun t ⟨_,kt⟩ =>
    ⟨ia.of_keeps kt (by decide),kt.sp.trans sp⟩

/-- Initialization establishes a common point and public counter in both runs. -/
theorem jointInit_relCT {C : Curve} {base T : Addr} {P Q : Point C} {u v : Nat}
    (hOne : cfg.K.one<C.p) :
    RelCT isa (JointCachePair C base T P Q u v)
      (.block (Jacobian.infinity cfg.K cfg.K.R++([.movz .x .x19 256 0] : List Instr)))
      (JointPair cfg C base 8192 (JointCore cfg C base 8192 Q u v
        (JointGenerator cfg C base 8192 P T)) .infinity 256) := by
  intro s t ts tt s' t' ⟨⟨E,hp⟩,ss,st,gs,gt⟩ es et
  obtain ⟨he,hp'⟩ := jointInit_fields hOne _ _ _ _ _ _ hp es et
  obtain ⟨_,_,xs,_,cs,s19⟩ := jointInit_ok hOne hp.left.to_tmv ss gs
  obtain ⟨_,_,xt,_,ct,t19⟩ := jointInit_ok hOne hp.right.to_tmv st gt
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  exact ⟨he,⟨_,hp'⟩,cs,ct,s19,t19⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
