module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect

/-! # DSA signing and verification for every AArch64 arithmetic backend -/

@[expose] public section

namespace VG.Generic.DsaArithmetic.AArch64.Dsa
open VG.Proof.Dsa.AArch64

def artifacts (v : Backend) : List Artifact := [
  Spec.Dsa.randomSignApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.RandomSign.code (randomSignerName v) (Impl.Dsa.AArch64.SignVerify.sign v.mul)
    stack := v.stack + 256
    verified := random_sign_verified v
    spSafe := random_sign_sp v
    features := v.features },
  Spec.Dsa.verifyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.SignVerify.verify v.mul
    stack := v.stack
    verified := v.verifyVerified
    spSafe := v.verifySp
    features := v.features },
  Spec.Dsa.validatePublicKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Prevalidated.validate v.mul
    stack := v.stack
    verified := v.validateVerified
    spSafe := v.validateSp
    features := v.features },
  Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Prevalidated.verify v.mul
    stack := v.stack
    verified := v.prevalidatedVerified
    spSafe := v.prevalidatedSp
    features := v.features },
  Spec.Dsa.generateKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
      (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveKey v.mul)
    stack := v.stack + 256
    verified := keygen_verified v
    spSafe := keygen_sp v
    features := v.features },
  Spec.Dsa.deriveKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Generate.deriveKey v.mul
    stack := v.stack
    verified := v.deriveVerified
    spSafe := v.deriveSp
    features := v.features }]

end VG.Generic.DsaArithmetic.AArch64.Dsa
