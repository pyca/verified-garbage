module

import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.DomainQRange
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ImportAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.OddCT
import VerifiedGarbage.Proof.Ffdh.Arm.Odd
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! The order's range and parity checks use fixed public addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (Operand)

theorem qRange_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots) (hasQ : p.hasQ = true) :
    RelCT isa (fun s t => ImportAtInput p slots s ∧ ImportAtInput p slots t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange (fun _ _ => True) := by
  let P := ArithmeticReady p.base p.len p.w
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have imported := importAt_ct (p := p) (slots := slots) (a := 1) (slot := 60) (countSlot := 32)
    (k := p.k) stable h60 h32 rfl (by decide)
  have wpImport (s : State) (h : ImportAtInput p slots s) :
      WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 60 32) s P :=
    WP.mono (importAt_ok s 1 60 32 h.context stable h60 h32 h.ready (by decide) (by decide)
      (h.context.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega)
      (by rw [p.qLength hasQ]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])) fun _ j => j.2.1
  have save := saveFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have finish := andFlag_ct.mono (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h)
  have wpRange (s : State) (h : P s) := inRange_ready s h op1 (by decide)
  have wpSave (s : State) (h : P s) := WP.mono (saveFlag_ok s h) fun _ j => j.1
  have wpOdd (s : State) (h : P s) := WP.mono (odd_ok s h (by decide : 1 < 8)) fun _ j => j.1
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange
  exact relCT_chain imported wpImport wpImport (relCT_chain (inRange_ct op1 (by decide)) wpRange wpRange
    (relCT_chain save wpSave wpSave (relCT_chain (odd_ct (by decide : 1 < 8)) wpOdd wpOdd finish)))

end VG.Proof.Ffdh.Arm
