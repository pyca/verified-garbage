module

public import VerifiedGarbage.Impl.AesSiv.X86
public import VerifiedGarbage.Proof.AesSiv.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86

/-! # AES-SIV (RFC 5297) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.X86

def artifacts : List Artifact :=
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

end VG.Artifacts.AesSiv.X86
