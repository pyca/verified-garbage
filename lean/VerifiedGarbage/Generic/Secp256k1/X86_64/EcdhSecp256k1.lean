import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Ecdh.X86_64.Secp256k1.Verified

/-! # secp256k1 on x86-64, generic over its proven group law and inversions -/

namespace VG.Generic.Secp256k1.X86_64.EcdhSecp256k1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  { Spec.Ecdh.Secp256k1.exchangeApi with
    target := X86_64.target
    doc := Spec.Ecdh.Secp256k1.exchangeApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), including for a = 0. \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdh.X86_64.exchangeSecp256k1
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst X86_64.abi
    verified := Proof.Ecdh.X86_64.Secp256k1.ecdh_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.Secp256k1.X86_64.EcdhSecp256k1
