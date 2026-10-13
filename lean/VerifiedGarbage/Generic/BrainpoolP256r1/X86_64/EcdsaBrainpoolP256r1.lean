module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-! # brainpoolP256r1 on x86-64, generic over its proven group law and inversions -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86_64.EcdsaBrainpoolP256r1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  { Spec.Ecdsa.BrainpoolP256r1.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.BrainpoolP256r1.signApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp256r1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by calls of `vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.X86_64.signBrainpoolP256r1
    contract := Spec.Ecdsa.BrainpoolP256r1.inst.signContract X86_64.abi 8
    stack := 8
    verified := Proof.Ecdsa.X86_64.BrainpoolP256r1.sign_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.BrainpoolP256r1.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.BrainpoolP256r1.verifyApi.doc (notes := ["Field elements are four 64-bit words in Montgomery form. \
      Scalar multiplication calls `vg_brainpoolp256r1_mul`, a fixed 256-iteration ladder with the general complete addition \
      formulas of Renes, Costello and Batina (Algorithm 1), which hold for any `a`. \
      Inversions use divsteps, by calls of `vg_brainpoolp256r1_inv_mod_p` and `vg_brainpoolp256r1_inv_mod_n`. \
      Branches and memory addresses depend only on pointers and loop counters."])
    code := Impl.Ecdsa.Verify.X86_64.verifyBrainpoolP256r1
    contract := Spec.Ecdsa.BrainpoolP256r1.inst.verifyContract X86_64.abi 8
    stack := 8
    verified := Proof.Ecdsa.Verify.X86_64.BrainpoolP256r1.verify_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.BrainpoolP256r1.X86_64.EcdsaBrainpoolP256r1
