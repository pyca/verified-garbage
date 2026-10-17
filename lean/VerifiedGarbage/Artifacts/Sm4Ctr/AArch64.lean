module

public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM4-CTR artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact AArch64.target {
    notes := ["Baseline AArch64: sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit (SM4's S-box is an affine map of AES's), with no table lookups; the key schedule's table of round keys is built once per call, by a call of `vg_sm4_prepare_keys`, and each batch is a call of `vg_sm4_crypt_prepared`."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr
    stack := 3264
    verified := Proof.Sm4.AArch64.ctr_framed }]

end VG.Artifacts.Sm4Ctr.AArch64
