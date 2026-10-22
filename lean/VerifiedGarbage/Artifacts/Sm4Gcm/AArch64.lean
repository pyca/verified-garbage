module

public import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.Ctr32Lit

/-! # SM4-GCM's counter mode on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact AArch64.target {
    notes := ["Baseline AArch64: `vg_sm4_ctr`'s code (sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups; the key schedule's table of round keys built once per call, by a call of `vg_sm4_prepare_keys`, and each batch a call of `vg_sm4_crypt_prepared`) with GCM's `inc₃₂` on the counter: the low 32 bits of the counter block's low half incremented by a 32-bit `add` and added back to its high 32 bits."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr32
    stack := 3264
    verified := Proof.Sm4.AArch64.ctr32_framed }]

end VG.Artifacts.Sm4Gcm.AArch64
