module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Prepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Prepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
public import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
public import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
public import VerifiedGarbage.Proof.AesGcm.CtxFrame
public import VerifiedGarbage.Proof.AesGcm.ScratchP
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Init
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchP
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.SealGather

/-!
# The instances of `seal` that `seal_gather` calls

`sealFn`: the code of `seal` for a variant, with its proof (given that of
GHASH's multiplication by the key, `MulKey`) and stack depth, for
`Generic/AesGcm/AArch64/AesGcm.lean`; `sealPreparedFn`, that of
`seal_prepared`, for `seal_gather_prepared`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn .plain :=
  .plain ⟨Spec.Gcm.sealApi.name ++ v.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)⟩
    (sealCode_framed v hMK) (sealCode_depth v)

/-- The instance of `vg_aes_gcm_seal_prepared` calling the implementations
`v`, and `gp` on the path for TLS records. -/
def sealPreparedFn (v : GcmImpl) (gp : GhashPreparedImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) :
    Proof.AesGcm.AArch64.Gather.SealFn .prepared :=
  .prepared ⟨"vg_aes_gcm_seal_prepared8" ++ v.suffix,
      Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn)⟩
    (Fast.sealPrepared_framed v gp hMK) (fastSealWith_depth v gp.noFrames)

end VG.Proof.AesGcm.AArch64
