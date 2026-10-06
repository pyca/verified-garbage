import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.Lit

/-!
# ECDSA over P-384 (FIPS 186-5) on x86-64

A generic file (see `TCB/Emit.lean`) over P-384's group law and
inversions `h`, the variant `Variants/P384/X86_64/Law.lean`.
-/

namespace VG.Generic.P384.X86_64.EcdsaP384

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P384.curve) : List Artifact := [
  { Spec.Ecdsa.P384.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P384.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are six 64-bit words in Montgomery form, \
      multiplied by word-by-word Montgomery multiplication (CIOS) with a final conditional \
      subtraction. `[k]G` is a fixed-base comb of 7-bit signed digits: the 55 windows `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 55 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P384_COMB` (330 KB), with no doublings: each entry is selected in constant time \
      by loading every entry of its table, 16 bytes at a time, and keeping (`pand`, `por`) the one \
      of the digit's magnitude (or the point at infinity for a zero digit), negated by a mask of \
      its sign, and added by the complete addition formulas of Renes, Costello and Batina for \
      `a = -3` (Algorithm 4); the \
      inversion modulo `p` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 \
      batches of 59 divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each \
      giving a matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the \
      coefficients `a`, `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 \
      divsteps in all, enough for 384-bit moduli by Bernstein and Yang's bound (which the proof \
      checks); then `f = ±1`, and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. \
      The number of steps is fixed, so the time does not depend on `Z`. `k⁻¹` modulo `n` is \
      Fermat's, by square-and-always-multiply over the bits of `n - 2`. The signature (or zeros) \
      is selected by a mask, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code := Impl.Ecdsa.X86_64.signP384
    contract := Spec.Ecdsa.P384.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts)
    verified := Proof.Ecdsa.X86_64.P384.sign_verified h.law (Proof.P384.combOk7 h.law) h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P384.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P384.verifyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, comb and inversions, with `vg_ecdh_p384`'s checks of the public \
      key and its window method: it saves its caller's callee-saved registers in `scratch`; field elements and scalars \
      are six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS) with a final conditional subtraction. The key is checked without \
      branches (its first byte, both coordinates below `p`, and the curve's equation), and \
      `[v]Q` is computed for the key's point if it is valid, else `G`, so it always runs on a \
      point of the curve. `s⁻¹` modulo `n` is Fermat's, by square-and-always-multiply, and `Z⁻¹` by the \
      signature's divsteps; `[u]G` is the signature's comb over the 7-bit windows of `u` (from the static `VG_P384_COMB`), and \
      `[v]Q` by `vg_ecdh_p384`'s signed 4-bit windows (`v` recoded as `v + 8 Σ_{j<97} 16^j`, \
      a table of `[1 … 8]Q` in `scratch`, four Jacobian doublings and a complete addition of \
      the entry selected in constant time per digit); the two are added by the complete \
      addition formulas of Renes, Costello and Batina. The result is the conjunction of the \
      checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` \
      modulo `n`) as a mask, so the time depends only on the pointers, although the contract would \
      let every input affect it."])
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    code := Impl.Ecdsa.Verify.X86_64.verifyP384
    contract := Spec.Ecdsa.P384.inst.verifyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts)
    verified := Proof.Ecdsa.Verify.X86_64.P384.verify_verified h.law (Proof.P384.combOk7 h.law) h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P384.X86_64.EcdsaP384
