module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA signing and verification for every AArch64 arithmetic backend -/

@[expose] public section

namespace VG.Generic.DsaArithmetic.AArch64.Dsa
open VG.Proof.Dsa.AArch64

def artifacts (v : Backend) : List Artifact := [
  Spec.Dsa.randomSignApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["Rejection sampling and signing retries are verified \
      against the bounded random-tape specification. The selected Montgomery backend is used \
      for each signing attempt. Every failure zeros the entire output."]
    code := Impl.Dsa.AArch64.RandomSign.code (randomSignerName v) (Impl.Dsa.AArch64.SignVerify.sign v.mul)
    stack := v.stack + 256
    verified := random_sign_verified v
    spSafe := random_sign_sp v
    features := v.features },
  Spec.Dsa.signApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signing derives public-key subgroup membership from g^q = 1 and g^x = y. \
      Scratch is initialized before use; every failure zeros the entire output."]
    code := Impl.Dsa.AArch64.SignVerify.sign v.mul
    stack := v.stack
    verified := v.signVerified
    spSafe := v.signSp
    features := v.features },
  Spec.Dsa.verifyApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signature scalars and the digest do not affect the leakage trace."]
    code := Impl.Dsa.AArch64.SignVerify.verify v.mul
    stack := v.stack
    verified := v.verifyVerified
    spSafe := v.verifySp
    features := v.features },
  Spec.Dsa.generateKeyApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["Checks the domain before consuming randomness, samples x with the \
      verified rejection sampler, then derives y = g^x with the selected Montgomery backend. \
      Every failure zeros the entire output."]
    code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
      (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveKey v.mul)
    stack := v.stack + 256
    verified := keygen_verified v
    spSafe := keygen_sp v
    features := v.features },
  Spec.Dsa.checkParametersApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["g^q mod p uses the selected Montgomery backend."]
    code := Impl.Dsa.AArch64.Generate.checkParameters v.mul
    stack := v.stack
    verified := v.parametersVerified
    spSafe := v.parametersSp
    features := v.features },
  Spec.Dsa.deriveKeyApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["y = g^x mod p uses the selected Montgomery backend. \
      Every failure zeros the entire output."]
    code := Impl.Dsa.AArch64.Generate.deriveKey v.mul
    stack := v.stack
    verified := v.deriveVerified
    spSafe := v.deriveSp
    features := v.features }]

end VG.Generic.DsaArithmetic.AArch64.Dsa
