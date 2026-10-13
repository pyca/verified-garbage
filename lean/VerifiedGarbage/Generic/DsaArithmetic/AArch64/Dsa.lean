module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
import VerifiedGarbage.Proof.Framework.AArch64.Call

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
      Scratch is initialized before use; every failure zeros the entire output. \
      Writes no callee-saved register and uses no stack."])
    code := Impl.Dsa.AArch64.SignVerify.sign v.mul
    contract := Spec.Dsa.signContract AArch64.abi
    verified := v.signVerified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Dsa.verifyApi with
    target := AArch64.target
    name := Spec.Dsa.verifyApi.name ++ v.suffix
    doc := Spec.Dsa.verifyApi.doc (notes := ["Fixed-window exponentiation and streaming modular reduction \
      use the selected Montgomery backend. Leading-zero component padding is supported. \
      Signature scalars and the digest do not affect the leakage trace. \
      Writes no callee-saved register and uses no stack."])
    code := Impl.Dsa.AArch64.SignVerify.verify v.mul
    contract := Spec.Dsa.verifyContract AArch64.abi
    verified := v.verifyVerified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.DsaArithmetic.AArch64.Dsa
