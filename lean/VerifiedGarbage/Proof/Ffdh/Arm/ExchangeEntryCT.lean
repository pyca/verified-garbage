module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The shared-secret entry uses fixed local and incoming stack slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) (fun _ _ => True) := by
  have accesses := RelCT.block_append ((storeLocal_ct .r0 4).seq (RelCT.block_append ((storeLocal_ct .r2 24).seq (RelCT.block_append ((storeLocal_ct .r3 28).seq (RelCT.block_append ((loadLocal_ct .r3 128 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 32).seq (RelCT.block_append ((loadLocal_ct .r3 132 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 40).seq (RelCT.block_append ((loadLocal_ct .r3 136 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 44).seq (RelCT.block_append ((loadLocal_ct .r3 140 (by decide)).seq (RelCT.block_append ((storeLocal_ct .r3 36).seq (RelCT.block_append ((loadLocal_ct .r0 148 (by decide)).seq ((storeLocal_ct .r0 0)))))))))))))))))))))))))
  exact (RelCT.block_append (stackAddr_ct.seq accesses)).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm
