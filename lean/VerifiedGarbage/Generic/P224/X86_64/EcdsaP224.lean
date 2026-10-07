import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.Lit

/-!
# ECDSA over P-224 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-224's group law and
inversions `h`, the variant `Variants/P224/X86_64/Law.lean`.
-/

namespace VG.Generic.P224.X86_64.EcdsaP224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact := [
  { Spec.Ecdsa.P224.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P224.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
      subtraction; the 28-byte encodings are read and written a word at a time, the top word's \
      four bytes from the first eight or a byte at a time. `[k]G` is a double-and-add ladder \
      over all 256 bits of the four words of `k`, with the complete addition formulas of Renes, \
      Costello and Batina for every addition and doubling and a masked selection for each bit; \
      the inversion modulo `p` is by divsteps (Bernstein and Yang's safegcd, half-delta form): \
      10 batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), \
      each giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 \
      divsteps in all, enough for 256-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is \
      Fermat's, by square-and-always-multiply over the bits of `n - 2`. The signature (or \
      zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.X86_64.signP224
    contract := Spec.Ecdsa.P224.inst.signContract X86_64.abi
    verified := Proof.Ecdsa.X86_64.P224.sign_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P224.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P224.verifyApi.doc (notes := ["The function is `vg_ecdsa_p224_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p224`'s checks of the public key \
      and its window method: it saves its caller's callee-saved registers in `scratch`; field \
      elements and scalars are four 64-bit words in Montgomery form, multiplied by word-by-word \
      Montgomery multiplication (CIOS) with a final conditional subtraction. The key is checked \
      without branches (its first byte, both coordinates below `p`, and the curve's equation), \
      and `[v]Q` is computed for the key's point if it is valid, else `G`, so it always runs on \
      a point of the curve. `s⁻¹` modulo `n` is Fermat's, by square-and-always-multiply, and \
      `Z⁻¹` by the signature's divsteps; `[u]G` is the signature's ladder over all 256 bits of \
      `u`, and `[v]Q` by `vg_ecdh_p224`'s signed 4-bit windows (`v` recoded as \
      `v + 8 Σ_{j<57} 16^j`, a table of `[1 … 8]Q` in `scratch`, four Jacobian doublings and a \
      complete addition of the entry selected in constant time per digit); the two are added \
      by the complete addition formulas of Renes, Costello and Batina. The result is the \
      conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at \
      infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, \
      although the contract would let every input affect it."])
    code := Impl.Ecdsa.Verify.X86_64.verifyP224
    contract := Spec.Ecdsa.P224.inst.verifyContract X86_64.abi
    verified := Proof.Ecdsa.Verify.X86_64.P224.verify_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P224.X86_64.EcdsaP224
