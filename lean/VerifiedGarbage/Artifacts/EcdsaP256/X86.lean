import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.Ecdsa.P256.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.Lit

/-! # ECDSA over P-256 (FIPS 186-5) on x86 (32-bit) -/

namespace VG.Artifacts.EcdsaP256.X86

def artifacts : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := X86.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      `ebx`, `esi`, `edi` and `ebp` in `scratch`. Field elements and scalars are eight 32-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`) with a final conditional subtraction. `[k]G` \
      is a double-and-add ladder over all 256 bits of `k`, with the complete addition formulas \
      of Renes, Costello and Batina for every addition and doubling and a masked selection for \
      each bit; the inversions modulo `p` and `n` are Fermat's, by square-and-always-multiply \
      over the bits of `p - 2` and `n - 2`. The signature (or zeros) is selected by a mask, so \
      the time depends only on the pointers."])
    code := Impl.Ecdsa.X86.signP256
    contract := Spec.Ecdsa.P256.inst.signContract X86.abi
    verified := Proof.Ecdsa.X86.sign_verified Proof.P256.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.EcdsaP256.X86
