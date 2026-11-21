module

public import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb8.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesOfb.X86_64.Final
public import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
public import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) => [
    Spec.Ofb.aesApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86_64.Fn.ofb v.level v.enc
      verified := Proof.Aes.X86_64.ModesScrub.ofb_scrubbed v
      spSafe := Proof.Aes.X86_64.ModesScrub.ofb_spSafeFn v },
    Spec.Ofb.aesFinalApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86_64.Fn.ofbFinal v.level v.enc v.suffix
      verified := Proof.Aes.X86_64.FinalScrub.ofbFinal_scrubbed v
      spSafe := Proof.Aes.X86_64.FinalScrub.ofbFinal_spSafeFn v }]

end VG.Artifacts.AesOfb.X86_64
