module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # DSA signing and verification for every AArch64 arithmetic backend -/

@[expose] public section

namespace VG.Generic.DsaArithmetic.AArch64.Dsa
open VG.Proof.Dsa.AArch64

def artifacts (v : Backend) : List Artifact := [
  { Spec.Dsa.signApi with
    target := AArch64.target
    name := Spec.Dsa.signApi.name ++ v.suffix
    doc := Spec.Dsa.signApi.doc (notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signing derives public-key subgroup membership from g^q = 1 and g^x = y. \
      Scratch is initialized before use; every failure zeros the entire output."])
    code := Impl.Dsa.AArch64.SignVerify.sign v.sq v.mul
    contract := Spec.Dsa.signContract AArch64.abi v.stack
    stack := v.stack
    verified := v.signVerified
    spSafe := v.signSp
    features := v.features },
  { Spec.Dsa.verifyApi with
    target := AArch64.target
    name := Spec.Dsa.verifyApi.name ++ v.suffix
    doc := Spec.Dsa.verifyApi.doc (notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signature scalars and the digest do not affect the leakage trace."])
    code := Impl.Dsa.AArch64.SignVerify.verify v.sq v.mul
    contract := Spec.Dsa.verifyContract AArch64.abi v.stack
    stack := v.stack
    verified := v.verifyVerified
    spSafe := v.verifySp
    features := v.features }]

end VG.Generic.DsaArithmetic.AArch64.Dsa
