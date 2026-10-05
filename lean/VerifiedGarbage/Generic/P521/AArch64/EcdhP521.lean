import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Verified

/-!
# ECDH over P-521 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/AArch64/Law.lean`.
-/

namespace VG.Generic.P521.AArch64.EcdhP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  { Spec.Ecdh.P521.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.P521.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p521_sign`'s \
      setup, field arithmetic and inversion, with the peer's point in place of `G`: it \
      saves the callee-saved registers `x19`–`x25` in `scratch`; field elements are \
      nine 64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and `umulh`, four of the multiplicand's words in registers and the other \
      five loaded for each word of the multiplier; each reduction step multiplies the \
      accumulator's low word by `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) \
      with a final conditional subtraction. The peer's key is checked without branches (its first \
      byte, both coordinates below `p`, and the curve's equation), and the scalar multiplication \
      runs on the peer's point if it is valid, else `G`, so always on a point of the curve. `[d]P` \
      is by signed 4-bit windows: `d + 8 Σ_{j<145} 16^j` gives 145 digits in `[-8, 7]`, a table of \
      `[1 … 8]P` is built in `scratch`, and each digit takes four doublings (in Jacobian \
      coordinates, dbl-2001-b, with `Y = 1` where the result is the point at infinity) and the \
      addition of its entry, every entry loaded and masked and `y` negated by a mask of the \
      digit's sign, by the complete formula of Renes, Costello and Batina for `a = -3` \
      (Algorithm 4); `Z⁻¹` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 1357 divsteps in all, enough for \
      576-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.AArch64.exchangeP521
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst AArch64.abi
    verified := Proof.Ecdh.AArch64.P521.ecdh_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P521.AArch64.EcdhP521
