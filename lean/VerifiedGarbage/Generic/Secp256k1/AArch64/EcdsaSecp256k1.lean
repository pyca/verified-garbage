import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Verified

/-! # secp256k1 on AArch64, generic over its proven group law and inversions -/

namespace VG.Generic.Secp256k1.AArch64.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  { Spec.Ecdsa.Secp256k1.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.Secp256k1.signApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.AArch64.signSecp256k1
    contract := Spec.Ecdsa.Secp256k1.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.Secp256k1.sign_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.Secp256k1.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.Secp256k1.verifyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.AArch64.Secp256k1.verify
    contract := Spec.Ecdsa.Secp256k1.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.Secp256k1.verify_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Secp256k1.AArch64.EcdsaSecp256k1
