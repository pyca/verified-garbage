module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Switching the active workspace leaks only the public stack address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_saveMain_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block saveMain) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 8])
      (fun s t => s.gpr .r12 = t.gpr .r12) := by
    apply single_ct (fun _ _ _ => rfl)
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, Option.some.injEq] at e1 e2
    subst u; subst v
    simp only [State.setReg, ite_true, h]
  have store : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12)
      (.block [.str .r0 .r12 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  exact RelCT.block_append (M := isa) (l₁ := [.addSp .r12 8]) (l₂ := [.str .r0 .r12 0]) (addr.seq store)

theorem crt_selectChild_ct (slot : Nat) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (selectChild slot) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (.block [.ldr .r0 .r0 slot]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  exact (relCT_keep_sp load (fun _ _ h => h.2)).seq activateWorkspace_ct

theorem crt_selectMain_ct : RelCT isa (fun s t => s.sp = t.sp) selectMain (fun _ _ => True) :=
  (loadStack_ct .r0 8).seq activateWorkspace_ct

end VG.Proof.Bignum.Arm
