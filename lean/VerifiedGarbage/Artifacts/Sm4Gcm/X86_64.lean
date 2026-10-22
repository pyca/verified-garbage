module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit

/-! # SM4-GCM's counter mode on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact X86_64.target {
    notes := ["Baseline x86-64: `vg_sm4_ctr`'s code (sixteen counter blocks at a time, encrypted bitsliced in general-purpose registers through the AES S-box circuit, with no table lookups; the round keys' table built once per call, inline, and each batch a call of `vg_sm4_crypt_prepared`) with GCM's `inc₃₂` on the counter: the low 32 bits of the counter block's low half incremented in a 32-bit register and added back to its high 32 bits."]
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr32
    stack := 3216
    verified := Proof.Sm4.X86_64.ctr32_framed }]

end VG.Artifacts.Sm4Gcm.X86_64
