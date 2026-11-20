module

public import VerifiedGarbage.Impl.AesCcm.X86
public import VerifiedGarbage.Proof.AesCcm.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-CCM (NIST SP 800-38C) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Ccm.sealApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86.Fn.«seal» v.callee v.suffix
      verified := .scrubbed (Proof.AesCcm.X86.Scrub.seal_scrubbed v)
      spSafe := Proof.AesCcm.X86.Scrub.seal_fnSpSafe v },
    Spec.Ccm.openApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCcm.X86.Fn.«open» v.callee v.suffix
      verified := .scrubbed (Proof.AesCcm.X86.Scrub.open_scrubbed v)
      spSafe := Proof.AesCcm.X86.Scrub.open_fnSpSafe v }]

end VG.Artifacts.AesCcm.X86
