module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneShot
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.AArch64.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenVerified

/-!
# The instances of `seal` and `open` that `seal_gather` and `open_to` call

`sealFn` and `openFn`: the code of `seal` and of `open` for a variant, with
its proof (given that of GHASH's multiplication by the key, `MulKey`) and
stack depth, for `Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG.Proof.AesGcm.AArch64

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.Gather.SealFn .plain :=
  .plain ⟨Spec.Gcm.sealApi.name ++ v.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2576 1 (sealCode v)⟩
    (sealCode_framed v hMK) (sealCode_depth v)

/-- The instance of `vg_aes_gcm_open` calling the implementations `v`, which
`vg_aes_gcm_open_to` calls. -/
def openFn (v : GcmImpl) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) : Proof.AesGcm.AArch64.OpenTo.OpenFn :=
  ⟨⟨Spec.Gcm.openApi.name ++ v.suffix, Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (openCode v)⟩,
    openCode_framed v hMK, openCode_depth v⟩

end VG.Proof.AesGcm.AArch64
