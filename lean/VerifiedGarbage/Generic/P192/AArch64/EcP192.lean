import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.EcKey.AArch64.P192.Verified

/-! # p192 on AArch64, generic over its proven group law and inversions -/

namespace VG.Generic.P192.AArch64.EcP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.EcKey.P192.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.P192.publicKeyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.EcKey.AArch64.publicKeyP192
    contract := Spec.EcKey.P192.inst.publicKeyContract AArch64.abi
    verified := Proof.EcKey.AArch64.P192.pk_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P192.AArch64.EcP192
