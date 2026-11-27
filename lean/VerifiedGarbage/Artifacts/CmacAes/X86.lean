module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Impl.CmacAes.Stream.X86
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on x86 -/

namespace VG.Artifacts.CmacAes.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.init v.expand v.callee v.suffix
      verified := Proof.CmacAes.Stream.X86.Scrub.init_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86.Scrub.init_fnSpSafe v },
    Spec.Cmac.aesAbsorbApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.absorb v.callee v.suffix
      verified := Proof.CmacAes.Stream.X86.Scrub.absorb_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86.Scrub.absorb_fnSpSafe v },
    Spec.Cmac.aesFinishApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.X86.Fn.finish v.callee v.suffix
      verified := Proof.CmacAes.Stream.X86.Scrub.finish_scrubbed v
      spSafe := Proof.CmacAes.Stream.X86.Scrub.finish_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.CmacAes.X86
