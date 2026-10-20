module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.Domain
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! The domain-check entry uses fixed stack addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem domainEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) (fun _ _ => True) := by
  have tail : RelCT isa LocalAddress
      (.block [.mov .r0 (.reg .r3), .str .r0 .r12 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  exact RelCT.block_append (stackAddr_ct.seq
    (RelCT.block_append ((storeLocal_ct .r0 24).seq
    (RelCT.block_append ((storeLocal_ct .r1 28).seq
    (RelCT.block_append ((storeLocal_ct .r2 32).seq tail)))))))

end VG.Proof.Ffdh.Arm
