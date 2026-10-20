module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpperCT
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecksCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The full scalar range check is constant time in the imported scalar. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand)

structure ScalarReady (p : Inputs) (slots : List Nat) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P

theorem scalarRange_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => ScalarReady p slots s ∧ ScalarReady p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange (fun _ _ => True) := by
  let P := ScalarReady p slots
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have nonzero := (nonzero_ct (base := p.base) (len := p.len) (w := p.w) op1).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  have wpNonzero (s : State) (h : P s) : WP isa (VG.Impl.Ffdh.Arm.nonzero 1) s P := by
    refine WP.mono (nonzero_ok s h.ready op1 (by decide)) ?_
    rintro u ⟨ready, _, arrays, frame, rest⟩
    exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1),
      ready, (arrays 0 op0 (by decide)).trans h.modulus⟩
  have save := saveFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.context.ptr.trans h.2.1.context.ptr.symm) (fun _ _ h => h)
  have wpSave (s : State) (h : P s) : WP isa (.block VG.Impl.Ffdh.Arm.saveFlag) s P := by
    refine WP.mono (saveFlag_ok s h.ready) ?_
    rintro u ⟨ready, _, arrays, frame, rest⟩
    exact ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at stable hd).1),
      ready, (arrays 0 (by decide)).trans h.modulus⟩
  have upper := (scalarUpper_ct stable h28 h32 h60).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context, h.1.ready⟩, ⟨h.2.1.context, h.2.1.ready⟩, h.2.2⟩) (fun _ _ h => h)
  have wpUpper (s : State) (h : P s) :=
    WP.mono (scalarUpper_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) fun _ j => j.2.1
  have finish := andFlag_ct.mono
    (P' := fun (s t : State) => ArithmeticReady p.base p.len p.w s ∧ ArithmeticReady p.base p.len p.w t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange
  exact relCT_chain nonzero wpNonzero wpNonzero
    (relCT_chain save wpSave wpSave (relCT_chain upper wpUpper wpUpper finish))

end VG.Proof.Ffdh.Arm
