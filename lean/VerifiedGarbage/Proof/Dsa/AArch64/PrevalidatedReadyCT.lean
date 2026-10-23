module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedBodyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.SizeBounds

/-! # The public schedule after independent verifying-workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedVerifyingCall => VerifyingShaped c.val))
      (seqs [SignVerify.workspaces, Prevalidated.compute M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq verifyingWorkspaces_ct ?_
  exact (prevalidatedBody_ct M).mono (fun _ _ h => verifyingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64
