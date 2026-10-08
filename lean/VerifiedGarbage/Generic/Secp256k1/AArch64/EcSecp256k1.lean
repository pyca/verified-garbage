import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Verified

/-! # secp256k1 on AArch64, generic over its proven group law and inversions -/

namespace VG.Generic.Secp256k1.AArch64.EcSecp256k1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  { Spec.EcKey.Secp256k1.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.Secp256k1.publicKeyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.EcKey.AArch64.publicKeySecp256k1
    contract := Spec.EcKey.Secp256k1.inst.publicKeyContract AArch64.abi
    verified := Proof.EcKey.AArch64.Secp256k1.pk_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Secp256k1.AArch64.EcSecp256k1
