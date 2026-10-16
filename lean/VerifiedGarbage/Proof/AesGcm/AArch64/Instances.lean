module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified

/-!
# The instance of `seal` that `seal_gather` calls

`sealFn`: the code of `seal` for a variant, with its proof (given that of
GHASH's multiplication by the key, `MulKey`) and stack depth, for
`Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn where
  fn := ⟨Spec.Gcm.sealApi.name ++ v.suffix,
    Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)⟩
  verified := sealCode_framed v hMK
  depth := sealCode_depth v

end VG.Proof.AesGcm.AArch64
