module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Prepared
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Prepared

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
  .prepared ⟨Spec.Gcm.sealPrepared8Api.name ++ v.suffix,
      Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (Impl.AesGcm.AArch64.Fast.sealWith v.callees gp.fn)⟩
    (Fast.sealPrepared_framed v gp hMK) (fastSealWith_depth v gp.noFrames)

end VG.Proof.AesGcm.AArch64
