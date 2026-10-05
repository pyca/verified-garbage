import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Verified

/-!
# ECDH over P-384 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/AArch64/Law.lean`.
-/

namespace VG.Generic.P384.AArch64.EcdhP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.Ecdh.P384.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.P384.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s \
      setup, field arithmetic and inversion, with the peer's point in place of `G`: it \
      saves the callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements are \
      six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and `umulh`, four of the multiplicand's words in registers and the other \
      two loaded for each word of the multiplier; each reduction step multiplies the \
      accumulator's low word by `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) \
      with a final conditional subtraction. The peer's key is checked without branches (its first \
      byte, both coordinates below `p`, and the curve's equation), and the scalar multiplication \
      runs on the peer's point if it is valid, else `G`, so always on a point of the curve. `[d]P` \
      is by signed 4-bit windows: `d + 8 Σ_{j<97} 16^j` gives 97 digits in `[-8, 7]`, a table of \
      `[1 … 8]P` is built in `scratch`, and each digit takes four doublings (in Jacobian \
      coordinates, dbl-2001-b, with `Y = 1` where the result is the point at infinity) and the \
      addition of its entry, every entry loaded and masked and `y` negated by a mask of the \
      digit's sign, by the complete formula of Renes, Costello and Batina for `a = -3` \
      (Algorithm 4); `Z⁻¹` is Fermat's, by \
      a chain of sliding 4-bit windows over `p - 2` (fixed by the code: 380 squarings and 79 \
      products by a table of odd powers). The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.Ecdh.AArch64.exchangeP384
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi
    verified := Proof.Ecdh.AArch64.P384.ecdh_verified h.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P384.AArch64.EcdhP384
