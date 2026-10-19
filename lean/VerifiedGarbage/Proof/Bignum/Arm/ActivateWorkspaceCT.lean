module

public import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Switching the active workspace leaks only the public stack address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem activateWorkspace_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block activateWorkspace) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 0])
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
  exact RelCT.block_append (M := isa) (l₁ := [.addSp .r12 0]) (l₂ := [.str .r0 .r12 0]) (addr.seq store)

end VG.Proof.Bignum.Arm
