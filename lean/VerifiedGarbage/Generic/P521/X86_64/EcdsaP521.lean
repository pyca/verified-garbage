import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Lit

/-!
# ECDSA over P-521 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86_64/Law.lean`.
-/

namespace VG.Generic.P521.X86_64.EcdsaP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.Ecdsa.P521.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P521.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are nine 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS, its accumulator in \
      `scratch`) with a final conditional subtraction; the 66-byte encodings are read and \
      written a word at a time, the top word's two bytes from the first eight or a byte at a \
      time, and the hash's integer is shifted right by its last 7 bits. `[k]G` is a \
      double-and-add ladder over all 576 bits of the nine words of `k`, with the complete \
      addition formulas of Renes, Costello and Batina for every addition and doubling and a \
      masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.X86_64.signP521
    contract := Spec.Ecdsa.P521.inst.signContract X86_64.abi
    verified := Proof.Ecdsa.X86_64.P521.sign_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P521.X86_64.EcdsaP521
