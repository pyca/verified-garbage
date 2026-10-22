module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit

/-!
# SM4-GCM on baseline x86-64: its counter mode and key setup

`vg_sm4_ctr32`, and `vg_sm4_gcm_init`, which calls it and
`vg_sm4_expand_key` and no implementation of `vg_ghash`, so that it is
registered once; the SM4-GCM functions that hash are generic over the
implementations of `vg_ghash` (`Generic/Ghash/X86_64/Sm4Gcm.lean`).
`vg_sm4_gcm_init` keeps its working space in a frame of 2568 bytes
(`Verified.stackScratch`), below which its calls use 3224, those of
`vg_sm4_ctr32`, whose frame takes 3208.
-/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact X86_64.target {
    notes := ["Baseline x86-64: `vg_sm4_ctr`'s code (sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups; the round keys' table built once per call, inline, and each batch a call of `vg_sm4_crypt_prepared`) with GCM's `inc₃₂` on the counter: the low 32 bits of the counter block's low half incremented in a 32-bit register and added back to its high 32 bits."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr32
    stack := 3216
    verified := Proof.Sm4.X86_64.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact X86_64.target {
    notes := ["This implementation expands the key with `vg_sm4_expand_key` and computes the hash subkey with `vg_sm4_ctr32`."]
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rdx Impl.Sm4Gcm.X86_64.init
    stack := 5792
    verified := Proof.Sm4Gcm.X86_64.init_framed
    spSafe := X86_64.withStackScratch_spSafe_of Proof.Sm4Gcm.X86_64.init_spSafe }]

end VG.Artifacts.Sm4Gcm.X86_64
