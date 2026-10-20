module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The public-check entry accesses only fixed local and incoming stack slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem checkPublicEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) (fun s t => s.sp = t.sp) := by
  have stores := RelCT.block_append ((storeLocal_ct .r0 24).seq
    (RelCT.block_append ((storeLocal_ct .r1 28).seq
    (RelCT.block_append ((storeLocal_ct .r2 32).seq
    (RelCT.block_append ((storeLocal_ct .r3 36).seq
    (RelCT.block_append ((loadLocal_ct .r0 132 (by decide)).seq (storeLocal_ct .r0 0))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq stores)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Ffdh.Arm
