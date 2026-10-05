import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Impl.Ecdsa.P384.X86
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Verified

/-!
# ECDSA over P-384 (FIPS 186-5) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/X86/Law.lean`.
-/

namespace VG.Generic.P384.X86.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.Ecdsa.P384.signApi with
    target := X86.target
    doc := Spec.Ecdsa.P384.signApi.doc (notes := ["The function saves the callee-saved registers \
      `ebx`, `esi`, `edi` and `ebp` in `scratch`. Field elements and scalars are twelve 32-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`) with a final conditional subtraction. `[k]G` \
      is a double-and-add ladder over all 384 bits of `k`, with the complete addition formulas \
      of Renes, Costello and Batina for every addition and doubling and a masked selection for \
      each bit; the inversions modulo `p` and `n` are Fermat's, by square-and-always-multiply \
      over the bits of `p - 2` and `n - 2`. The signature (or zeros) is selected by a mask, so \
      the time depends only on the pointers."])
    code := Impl.Ecdsa.X86.signP384
    contract := Spec.Ecdsa.P384.inst.signContract X86.abi
    verified := Proof.Ecdsa.X86.P384.sign_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P384.verifyApi with
    target := X86.target
    doc := Spec.Ecdsa.P384.verifyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p384`'s checks of the public key: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements \
      and scalars are twelve 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`) with a final conditional \
      subtraction. The key is checked without branches (its first byte, both coordinates below \
      `p`, and the curve's equation), and the second ladder multiplies the key's point if it is \
      valid, else `G`, so it always runs on a point of the curve. `s⁻¹` modulo `n` and `Z⁻¹` are \
      Fermat's, by square-and-always-multiply; `[u]G` and `[v]Q` are double-and-add ladders over \
      all 384 bits of `u` and `v`, with the complete addition formulas of Renes, Costello and \
      Batina, which also add the two. The result is the conjunction of the checks (the key, `r` \
      and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a \
      mask, so the time depends only on the pointers, although the contract would let every \
      input affect it."])
    code := Impl.Ecdsa.Verify.X86.verifyP384
    contract := Spec.Ecdsa.P384.inst.verifyContract X86.abi
    verified := Proof.Ecdsa.Verify.X86.P384.verify_verified h.law
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P384.X86.EcdsaP384
