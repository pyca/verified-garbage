module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Retaining the appended context reads and writes only fixed stack offsets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem cachedKeyGenerateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.CachedKeyGenerate.entry) (fun _ _ => True) := by
  have extra := RelCT.block_append (stackAddr_ct.seq (RelCT.block_append
    ((loadLocal_ct .r3 156 (by decide)).seq (storeLocal_ct .r3 52))))
  exact RelCT.block_append ((relCT_keep_sp keyEntry_ct (fun _ _ h => h)).seq
    (extra.mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm
