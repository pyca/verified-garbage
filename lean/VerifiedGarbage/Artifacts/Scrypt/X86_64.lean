module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Scrub
import VerifiedGarbage.Impl.Scrypt.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha256Compress.X86_64
import VerifiedGarbage.Proof.Variants.ScryptRoMix.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on x86-64 -/

namespace VG.Artifacts.Scrypt.X86_64

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_scrubbed scrypt_spSafeFn)

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.ScryptRoMix.X86_64.variants.flatMap fun (R : Proof.Scrypt.X86_64.Whole.RMImpl) =>
  VG.Proof.Variants.Sha256Compress.X86_64.variants.flatMap fun (c : Proof.Sha256.X86_64.Compress) => [
    Spec.Scrypt.scryptApi.artifact X86_64.target {
      suffix := c.suffix ++ R.suffix
      notWith := R.notWith
      code := Impl.Scrypt.X86_64.Fn.scrypt (c.level.join R.level) R.name R.code (pbkName c) (pbkOf c)
      verified := Proof.Scrypt.X86_64.Whole.scrypt_scrubbed c R
      spSafe := Proof.Scrypt.X86_64.Whole.scrypt_spSafeFn c R }]

spec_apis artifacts

end VG.Artifacts.Scrypt.X86_64
