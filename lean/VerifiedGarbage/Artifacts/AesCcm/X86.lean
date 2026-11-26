module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Impl.AesCcm.X86
import VerifiedGarbage.Proof.AesCcm.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on x86 -/

namespace VG.Artifacts.AesCcm.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Ccm.sealApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86.Fn.«seal» v.callee v.suffix
      verified := Proof.AesCcm.X86.Scrub.seal_scrubbed v
      spSafe := Proof.AesCcm.X86.Scrub.seal_fnSpSafe v },
    Spec.Ccm.openApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86.Fn.«open» v.callee v.suffix
      verified := Proof.AesCcm.X86.Scrub.open_scrubbed v
      spSafe := Proof.AesCcm.X86.Scrub.open_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesCcm.X86
