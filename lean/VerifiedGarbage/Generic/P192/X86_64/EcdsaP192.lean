import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P192.Verified

/-! # p192 on x86-64, generic over its proven group law and inversions -/

namespace VG.Generic.P192.X86_64.EcdsaP192

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.Ecdsa.P192.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P192.signApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.X86_64.signP192
    contract := Spec.Ecdsa.P192.inst.signContract X86_64.abi
    verified := Proof.Ecdsa.X86_64.P192.sign_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P192.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P192.verifyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.X86_64.verifyP192
    contract := Spec.Ecdsa.P192.inst.verifyContract X86_64.abi
    verified := Proof.Ecdsa.Verify.X86_64.P192.verify_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P192.X86_64.EcdsaP192
