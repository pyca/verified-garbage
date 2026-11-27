module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Impl.AesOfb.X86.Final
import VerifiedGarbage.Proof.AesOfb.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86 -/

namespace VG.Artifacts.AesOfb.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ofb.aesApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86.Fn.crypt (Proof.AesOfb.X86.cryptCode v)
      verified := Proof.AesOfb.X86.Scrub.ofb_scrubbed v
      spSafe := Proof.AesOfb.X86.Scrub.ofb_fnSpSafe v },
    Spec.Ofb.aesFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86.Fn.cryptFinal (Proof.AesOfb.X86.cryptCode v) v.enc v.suffix
      verified := Proof.AesOfb.X86.Scrub.ofbFinal_scrubbed v
      spSafe := Proof.AesOfb.X86.Scrub.ofbFinal_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesOfb.X86
