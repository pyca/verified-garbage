import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoop

/-! The joint scalar loop with an explicit internal register and byte frame.

Only the loop counter must survive its arithmetic blocks. The outer verifier
is responsible for restoring any additional ABI registers after the loop.
-/
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
      AllocatedFrame rs base W s t ∧ Core (add A (FastNaf.point C P 7 u j)) t

theorem allocatedJointDigits_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v j : Nat}
    (hC : Law C) (hQ : onCurve C Q=true) (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v)
    {A : Point C} (hA : onCurve C A=true) {s : State} (hs : Core A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.digits c o) s fun t => AllocatedFrame rs base W s t ∧
      Core (add (add A (FastNaf.point C Q 5 v j)) (FastNaf.point C P 7 u j)) t := by
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
    {s : State} (hs : Core (jointPoint P Q u v (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Joint.step c o) s fun t => AllocatedFrame (.x19::rs) base W s t ∧
      Core (jointPoint P Q u v j) t ∧ t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Joint.step]
  apply WP.seq
  refine WP.mono_syms (decCounter_ok s (by omega) (by omega) h19) fun a ⟨a19,ka⟩ hsym => ?_
  have ca := hops.keep _ s a ka hsym hs
  apply WP.seq
  refine WP.mono (hops.double _ a (jointPoint_curve hC hP hQ u v (j+1)) ca) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.regs.gpr _ hops.counter,a19,Nat.add_sub_cancel]
  refine WP.mono (allocatedJointDigits_ok hC hQ hops
    (hC.onCurve_add (jointPoint_curve hC hP hQ u v (j+1)) (jointPoint_curve hC hP hQ u v (j+1)))
    cb (by omega) b19) fun t ⟨kt,ct⟩ => ?_
  rw [jointPoint_step hC hP hQ] at ct
  have kp := kb.trans kt
  refine ⟨⟨(Keeps.regs ka).mono (by simp) |>.trans
    (kp.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr)),?_⟩,ct,?_⟩
  · simpa only [ka.mem] using kp.unch
  · rw [kt.regs.gpr _ hops.counter,b19]

theorem allocatedJointLoop_ok {c : Joint.Cfg} {o : Joint.Ops} {C : Curve} {base : Addr}
    {rs : List Reg} {W : List (Nat × Nat)} {Core : Point C → State → Prop} {P Q : Point C} {u v : Nat}
    (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hops : AllocatedJointOpsOk c o C base rs W Core P Q u v)
    {s : State} (hs : Core (jointPoint P Q u v 256) s) (h19 : s.gpr .x19=256) :
    WP isa (.loop (Joint.step c o) (.nonzero .x .x19)) s fun t =>
      AllocatedFrame (.x19::rs) base W s t ∧ Core (add (mul u P) (mul v Q)) t ∧ t.gpr .x19=0 := by
  let I := fun j t => AllocatedFrame (.x19::rs) base W s t ∧
    Core (jointPoint P Q u v j) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv:=I) (n:=256) (by decide)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have he : j-1+1=j := by omega
    refine WP.mono (allocatedJointStep_ok hC hP hQ hops (by omega) (he.symm ▸ ca) (he.symm ▸ a19))
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    rw [jointPoint_zero] at ct
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
  have he := jointPoint_step hC hP hQ u v 256
  rw [jointPoint_top P Q hu hv] at he
  change add (add .infinity (FastNaf.point C Q 5 v 256))
    (FastNaf.point C P 7 u 256)=jointPoint P Q u v 256 at he
  rw [he] at ca
  refine WP.mono (allocatedJointLoop_ok hC hP hQ hops ca
    ((ka.regs.gpr _ hops.counter).trans h19)) fun t ⟨kt,ct,t19⟩ =>
      ⟨(ka.widenRegs (fun _ hr => List.mem_cons_of_mem _ hr)).trans kt,ct,t19⟩

end VG.Proof.Weierstrass.AArch64
