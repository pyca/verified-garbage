module

public import VerifiedGarbage.Impl.AesCtr.X86.Final
public import VerifiedGarbage.Proof.AesCtr.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Ctr.aesApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86.Fn.crypt32 v.callee
      verified := Proof.AesCtr.X86.Scrub.ctr_scrubbed v
      spSafe := Proof.AesCtr.X86.Scrub.ctr_fnSpSafe v }]) ++
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ctr.aesFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCtr.X86.Fn.cryptFinal v.enc v.suffix
      verified := Proof.AesCtr.X86.Scrub.ctrFinal_scrubbed v
      spSafe := Proof.AesCtr.X86.Scrub.ctrFinal_fnSpSafe v }]

end VG.Artifacts.AesCtr.X86
