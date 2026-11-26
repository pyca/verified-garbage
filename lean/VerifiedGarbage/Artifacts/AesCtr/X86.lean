module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Impl.AesCtr.X86.Final
import VerifiedGarbage.Proof.AesCtr.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Variants.AesCtr32.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

namespace VG.Artifacts.AesCtr.X86

public def artifacts : List (Artifact X86.target) :=
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

spec_apis artifacts

end VG.Artifacts.AesCtr.X86
