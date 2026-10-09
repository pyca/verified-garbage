import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.EcKey.X86_64.P192.Verified

/-! # p192 on x86-64, generic over its proven group law and inversions -/

namespace VG.Generic.P192.X86_64.EcP192

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact := [
  { Spec.EcKey.P192.publicKeyApi with
    target := X86_64.target
    doc := Spec.EcKey.P192.publicKeyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication uses a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1). \
      Inversions use divsteps. Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.EcKey.X86_64.publicKeyP192
    contract := Spec.EcKey.P192.inst.publicKeyContract X86_64.abi
    verified := Proof.EcKey.X86_64.P192.pk_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P192.X86_64.EcP192
