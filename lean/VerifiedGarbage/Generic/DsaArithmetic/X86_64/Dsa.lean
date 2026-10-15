module

public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignVerified
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingVerified
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT

/-! # DSA signing and verification for every x86-64 arithmetic backend -/

@[expose] public section

namespace VG.Generic.DsaArithmetic.X86_64.Dsa
open VG.Proof.Dsa.X86_64

def artifacts (v : Backend) : List Artifact := [
  { Spec.Dsa.randomSignApi with
    target := X86_64.target
    name := Spec.Dsa.randomSignApi.name ++ v.suffix
    doc := Spec.Dsa.randomSignApi.doc (notes := ["Rejection sampling and signing retries are verified \
      against the bounded random-tape specification. The selected Montgomery backend is used \
      for each signing attempt. Every failure zeros the entire output."])
    code := Impl.Dsa.X86_64.RandomSign.code (randomSignerName v) (Impl.Dsa.X86_64.SignVerify.sign v.mul)
    contract := Spec.Dsa.randomSignContract X86_64.abi (v.stack + 256)
    stack := v.stack + 256
    verified := random_sign_verified v
    spSafe := random_sign_sp v
    features := v.features },
  { Spec.Dsa.signApi with
    target := X86_64.target
    name := Spec.Dsa.signApi.name ++ v.suffix
    doc := Spec.Dsa.signApi.doc (notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signing derives public-key subgroup membership from g^q = 1 and g^x = y. \
      Scratch is initialized before use; every failure zeros the entire output."])
    code := Impl.Dsa.X86_64.SignVerify.sign v.mul
    contract := Spec.Dsa.signContract X86_64.abi v.stack
    stack := v.stack
    verified := v.signVerified
    spSafe := v.signSp
    features := v.features },
  { Spec.Dsa.verifyApi with
    target := X86_64.target
    name := Spec.Dsa.verifyApi.name ++ v.suffix
    doc := Spec.Dsa.verifyApi.doc (notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signature scalars and the digest do not affect the leakage trace."])
    code := Impl.Dsa.X86_64.SignVerify.verify v.mul
    contract := Spec.Dsa.verifyContract X86_64.abi v.stack
    stack := v.stack
    verified := v.verifyVerified
    spSafe := v.verifySp
    features := v.features }]

end VG.Generic.DsaArithmetic.X86_64.Dsa
