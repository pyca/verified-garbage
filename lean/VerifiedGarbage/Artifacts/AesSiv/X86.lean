module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Impl.AesSiv.X86
import VerifiedGarbage.Proof.AesSiv.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on x86 -/

namespace VG.Artifacts.AesSiv.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesCtr32.X86.variants.flatMap fun (v : Proof.Aes.X86.Ctr32Impl) => [
    Spec.Siv.initApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesSiv.X86.Fn.init v.expand v.callee v.suffix
      verified := Proof.AesSiv.X86.Scrub.init_scrubbed v
      spSafe := Proof.AesSiv.X86.Scrub.init_fnSpSafe v },
    Spec.Siv.encryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesSiv.X86.Fn.encrypt v.callee v.suffix
      verified := Proof.AesSiv.X86.Scrub.encrypt_scrubbed v
      spSafe := Proof.AesSiv.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Siv.decryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesSiv.X86.Fn.decrypt v.callee v.suffix
      verified := Proof.AesSiv.X86.Scrub.decrypt_scrubbed v
      spSafe := Proof.AesSiv.X86.Scrub.decrypt_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesSiv.X86
