module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyVerified
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCorrect

/-! # DSA signing and verification for every x86-64 arithmetic backend -/

@[expose] public section

namespace VG.Generic.DsaArithmetic.X86_64.Dsa
open VG.Proof.Dsa.X86_64

def artifacts (v : Backend) : List Artifact := [
  Spec.Dsa.randomSignApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["Rejection sampling and signing retries are verified \
      against the bounded random-tape specification. The selected Montgomery backend is used \
      for each signing attempt. Every failure zeros the entire output."]
    code := Impl.Dsa.X86_64.RandomSign.code (randomSignerName v) (Impl.Dsa.X86_64.SignVerify.sign v.sq v.mul)
    stack := v.stack + 256
    verified := random_sign_verified v
    spSafe := random_sign_sp v
    features := v.features },
  Spec.Dsa.signApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signing derives public-key subgroup membership from g^q = 1 and g^x = y. \
      Scratch is initialized before use; every failure zeros the entire output."]
    code := Impl.Dsa.X86_64.SignVerify.sign v.sq v.mul
    stack := v.stack
    verified := v.signVerified
    spSafe := v.signSp
    features := v.features },
  Spec.Dsa.verifyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signature scalars and the digest do not affect the leakage trace."]
    code := Impl.Dsa.X86_64.SignVerify.verify v.sq v.mul
    stack := v.stack
    verified := v.verifyVerified
    spSafe := v.verifySp
    features := v.features },
  Spec.Dsa.generateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["Checks the domain before consuming randomness, samples x with the \
      verified rejection sampler, then derives y = g^x with the selected Montgomery backend. \
      Every failure zeros the entire output."]
    code := Impl.Dsa.X86_64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
      (Impl.Dsa.X86_64.Generate.checkParameters v.sq v.mul) (Impl.Dsa.X86_64.Generate.deriveKey v.sq v.mul)
    stack := v.stack + 256
    verified := keygen_verified v
    spSafe := keygen_sp v
    features := v.features },
  Spec.Dsa.checkParametersApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["g^q mod p uses the selected Montgomery backend."]
    code := Impl.Dsa.X86_64.Generate.checkParameters v.sq v.mul
    stack := v.stack
    verified := v.parametersVerified
    spSafe := v.parametersSp
    features := v.features },
  Spec.Dsa.deriveKeyApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["y = g^x mod p uses the selected Montgomery backend. \
      Every failure zeros the entire output."]
    code := Impl.Dsa.X86_64.Generate.deriveKey v.sq v.mul
    stack := v.stack
    verified := v.deriveVerified
    spSafe := v.deriveSp
    features := v.features }]

end VG.Generic.DsaArithmetic.X86_64.Dsa
