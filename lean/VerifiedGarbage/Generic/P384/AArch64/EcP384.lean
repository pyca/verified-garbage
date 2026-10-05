import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Impl.EcKey.P384.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified

/-!
# P-384 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/AArch64/Law.lean`.
-/

namespace VG.Generic.P384.AArch64.EcP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  { Spec.EcKey.P384.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.P384.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      the callee-saved registers `x19`–`x25` in `scratch`; field elements are six \
      64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and `umulh`, four of the multiplicand's words in registers and the other two \
      loaded for each word of the multiplier; each reduction step multiplies the accumulator's low \
      word by `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) with a final conditional subtraction; \
      `[d]G` is `vg_ecdsa_p384_sign`'s fixed-base comb of 7-bit signed digits from the 55 tables \
      of `[m 2^(7j)]G` (`m = 1 … 64`) in the static `VG_P384_COMB`, each entry selected in \
      constant time by loading the whole table, with no doublings; and \
      `Z⁻¹` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 divsteps in all, enough for \
      384-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.AArch64.p384.combConsts
    code := Impl.EcKey.AArch64.publicKeyP384
    contract := Spec.EcKey.P384.inst.publicKeyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p384.combConsts)
    verified := Proof.EcKey.AArch64.P384.pk_verified h.law h.inv (Proof.P384.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P384.AArch64.EcP384
