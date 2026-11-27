module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Impl.AesEcb.X86
import VerifiedGarbage.Proof.AesEcb.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-ECB (NIST SP 800-38A §6.1) on x86 -/

namespace VG.Artifacts.AesEcb.X86

open VG.Proof.AesEcb.X86.Scrub

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.AesEcb.encryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.Fn.crypt (ecbFree v.enc v.encWritten) v.enc v.encWritten
      verified := Proof.AesEcb.X86.Scrub.encrypt_scrubbed v
      publicOutOk := Proof.AesEcb.X86.Scrub.encrypt_public v
      spSafe := Proof.AesEcb.X86.Scrub.encrypt_fnSpSafe v },
    Spec.AesEcb.decryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesEcb.X86.Fn.crypt (ecbFree v.dec v.decWritten) v.dec v.decWritten
      verified := Proof.AesEcb.X86.Scrub.decrypt_scrubbed v
      publicOutOk := Proof.AesEcb.X86.Scrub.decrypt_public v
      spSafe := Proof.AesEcb.X86.Scrub.decrypt_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesEcb.X86
