module

public import VerifiedGarbage.Proof.Ffdh.Arm.Branch
public import VerifiedGarbage.Proof.Ffdh.Arm.QTest
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The small branch-control blocks have fixed traces. Branch conditions are
related separately from the values moved by these blocks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem ret_ct (n : BitVec 32) : RelCT isa (fun _ _ => True)
    (VG.Impl.Ffdh.Arm.Domain.ret n) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (hc := .block []) (by rfl)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem finishFlag_ct : RelCT isa (fun _ _ => True)
    VG.Impl.Ffdh.Arm.Domain.finishFlag (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem testFlag_ct : RelCT isa (fun _ _ => True)
    VG.Impl.Ffdh.Arm.Domain.testFlag (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

theorem qTest_ct : RelCT isa (fun s t => s.sp = t.sp)
    VG.Impl.Ffdh.Arm.Domain.qTest (fun s t => s.sp = t.sp) := by
  have tail : RelCT isa (fun s t => s.sp = t.sp) (.block [
      .dp .sub .r3 .r3 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .cmp .r3 (.imm 0)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((stackLoads_ct [(.r3, 28), (.r4, 32)]).seq
    (relCT_keep_sp tail (fun _ _ h => h)))

theorem iteKnown_ct {P : State → Prop} {c : Cond} {yes no : Prog isa} (b : Bool)
    (condition : ∀ s, P s → eval c s = some b)
    (taken : b = true → RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) yes (fun _ _ => True))
    (other : b = false → RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) no (fun _ _ => True)) :
    RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (.ite c yes no) (fun _ _ => True) := by
  apply RelCT.ite (fun s t h => (condition s h.1).trans (condition t h.2.1).symm)
  · intro s t tr1 tr2 u v h e1 e2
    have selected : b = true := Option.some.inj ((condition s h.1.1).symm.trans h.2)
    exact taken selected s t tr1 tr2 u v h.1 e1 e2
  · intro s t tr1 tr2 u v h e1 e2
    have selected : b = false := Option.some.inj ((condition s h.1.1).symm.trans h.2)
    exact other selected s t tr1 tr2 u v h.1 e1 e2

end VG.Proof.Ffdh.Arm
