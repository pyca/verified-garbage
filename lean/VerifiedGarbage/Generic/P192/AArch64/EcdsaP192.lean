import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified

/-! # p192 on AArch64, generic over its proven group law and inversions -/

namespace VG.Generic.P192.AArch64.EcdsaP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.Ecdsa.P192.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P192.signApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.AArch64.signP192
    contract := Spec.Ecdsa.P192.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.P192.sign_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P192.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P192.verifyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.AArch64.P192.verify
    contract := Spec.Ecdsa.P192.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.P192.verify_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P192.AArch64.EcdsaP192
