module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Scrub
public import VerifiedGarbage.Impl.Scrypt.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Sha256Compress.X86_64
public import VerifiedGarbage.Proof.Variants.ScryptRoMix.X86_64

/-! # scrypt (RFC 7914) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86_64

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_scrubbed scrypt_spSafeFn)

def artifacts : List Artifact :=
  VG.Proof.Variants.ScryptRoMix.X86_64.variants.flatMap fun (R : Proof.Scrypt.X86_64.Whole.RMImpl) =>
  VG.Proof.Variants.Sha256Compress.X86_64.variants.flatMap fun (c : Proof.Sha256.X86_64.Compress) => [
    Spec.Scrypt.scryptApi.artifact X86_64.target {
      suffix := c.suffix ++ R.suffix
      notWith := R.notWith
      code := Impl.Scrypt.X86_64.Fn.scrypt (c.level.join R.level) R.name R.code (pbkName c) (pbkOf c)
      verified := .scrubbed (scrypt_scrubbed c R)
      spSafe := scrypt_spSafeFn c R }]

end VG.Artifacts.Scrypt.X86_64
