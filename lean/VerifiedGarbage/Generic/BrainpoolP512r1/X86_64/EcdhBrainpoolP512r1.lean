module

import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-! # brainpoolP512r1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86_64.EcdhBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact := [
  { Spec.Ecdh.BrainpoolP512r1.exchangeApi with
    target := X86_64.target
    doc := Spec.Ecdh.BrainpoolP512r1.exchangeApi.doc (notes := ["Field elements are eight 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp512r1_mul`, a fixed 512-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by a call of `vg_brainpoolp512r1_inv_mod_p`. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdh.X86_64.exchangeBrainpoolP512r1
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP512r1.inst X86_64.abi 8
    stack := 8
    verified := Proof.Ecdh.X86_64.BrainpoolP512r1.ecdh_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.BrainpoolP512r1.X86_64.EcdhBrainpoolP512r1
