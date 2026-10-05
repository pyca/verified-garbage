import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.HasLaw
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified

/-!
# ECDH over P-256 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcdhP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLaw Spec.P256.curve) : List Artifact := [
  { Spec.Ecdh.P256.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s \
      setup, field arithmetic and inversion, with the peer's point in place of `G`: it \
      saves the callee-saved registers `x19`–`x25` in `scratch`; field elements are \
      four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and `umulh` and the multiplicand's words in registers; modulo `p`, `p ≡ -1 \
      (mod 2⁶⁴)`, so each step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts and one product) \
      with a final conditional subtraction. The peer's key is checked without branches (its first \
      byte, both coordinates below `p`, and the curve's equation), and the scalar multiplication \
      runs on the peer's point if it is valid, else `G`, so always on a point of the curve. `[d]P` \
      is by signed 4-bit windows: `d + 8 Σ_{j<65} 16^j` gives 65 digits in `[-8, 7]`, a table of \
      `[1 … 8]P` is built in `scratch`, and each digit takes four doublings (in Jacobian \
      coordinates, dbl-2001-b, with `Y = 1` where the result is the point at infinity) and the \
      addition of its entry, every entry loaded and masked and `y` negated by a mask of the \
      digit's sign, by the complete formula of Renes, Costello and Batina for `a = -3` \
      (Algorithm 4); `Z⁻¹` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 divsteps in all, enough for \
      256-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.AArch64.exchangeP256
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi
    verified := Proof.Ecdh.AArch64.ecdh_verified h.law h.inv
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcdhP256
