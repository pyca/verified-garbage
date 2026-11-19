module

public import VerifiedGarbage.Proof.AesCtr.X86.Ctr32
public import VerifiedGarbage.Proof.AesCtr.X86.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86

open VG.Proof.AesCtr.X86 VG.Proof.AesCtr.X86.Ctr32

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86.variants.map fun (v : Proof.Aes.X86.Ctr32Impl) =>
    Spec.Ctr.aesApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86.crypt32 v.callee
      verified := .unscrubbed (Proof.AesCtr.keyed (crypt32_verified v))
      spSafe := crypt32_spSafe v }) ++
  VG.Proof.Variants.AesBlocks.X86.variants.map fun (v : Proof.Aes.X86.BlocksImpl) =>
    Spec.Ctr.aesFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86.withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal v.enc v.suffix)
      verified := .unscrubbed (Proof.AesCtr.final_keyed (cryptFinal_framed v))
      spSafe := cryptFinal_framed_spSafe v }

end VG.Artifacts.AesCtr.X86
