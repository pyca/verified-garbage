module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
import VerifiedGarbage.Impl.AesCfb8.X86_64.Fn
import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
import VerifiedGarbage.Proof.AesOfb.X86_64.Final
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86-64 -/

namespace VG.Artifacts.AesOfb.X86_64

public def artifacts : List (Artifact X86_64.target) :=
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

spec_apis artifacts

end VG.Artifacts.AesOfb.X86_64
