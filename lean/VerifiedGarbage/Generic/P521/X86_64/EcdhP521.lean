import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit

/-!
# ECDH over P-521 (SP 800-56A) on x86-64

A generic file (see `TCB/Emit.lean`) over P-521's group law and
inversions `h`, the variant
`Variants/P521/X86_64/Law.lean`.
-/

namespace VG.Generic.P521.X86_64.EcdhP521

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P521.curve) : List Artifact := [
  { Spec.Ecdh.P521.exchangeApi with
    target := X86_64.target
    doc := Spec.Ecdh.P521.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p521_sign`'s setup, \
      field arithmetic and inversion, with the peer's point in place of `G`: it saves its \
      caller's callee-saved registers in `scratch`; field elements are nine 64-bit words in \
      Montgomery form, multiplied by Montgomery multiplication by columns (product \
      scanning, the accumulator in three registers; as `p = 2⁵²¹ - 1 ≡ -1 (mod 2⁶⁴)`, each \
      reduction's multiplier is its column's low word, added 512 times eight columns up; \
      a square computes each product of two different words once and adds it twice) with a final \
      conditional subtraction. The peer's key is checked without branches (its first byte, both \
      coordinates below `p`, and the curve's equation), and `[d]P` is computed for the peer's \
      point if it is valid, else `G`, so it always runs on a point of the curve. `[d]P` is by \
      signed 4-bit windows: `d` is recoded as `d + 8 Σ_{j<145} 16^j`, whose 145 nibbles less 8 \
      are digits in `[-8, 7]`; a table of `[1 … 8]P` is built in `scratch` by complete \
      additions; then, from the point at infinity, for each digit from the top, four doublings \
      in Jacobian coordinates (dbl-2001-b, for `a = -3`) and the addition of the digit's entry, \
      selected in constant time by loading all eight entries, 16 bytes at a time (each entry's \
      27 words as 14 pieces, the last two overlapping by a word), and keeping (`pand`, `por`) \
      the one of the digit's magnitude, and negated by a mask of its sign, by the complete \
      addition formulas of Renes, Costello and Batina for `a = -3` (Algorithm 4); `Z⁻¹` is by \
      the signature's divsteps. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.X86_64.exchangeP521
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi
    verified := Proof.Ecdh.X86_64.P521.ecdh_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P521.X86_64.EcdhP521
