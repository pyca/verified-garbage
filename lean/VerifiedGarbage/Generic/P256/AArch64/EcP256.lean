import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.EcKey.P256.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.Verified

/-!
# P-256 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.P256.AArch64.EcP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  { Spec.EcKey.P256.publicKeyApi with
    target := AArch64.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      the callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements are four \
      64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and `umulh` and the multiplicand's words in registers; modulo `p`, `p ≡ -1 (mod \
      2⁶⁴)`, so each step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts and one product) with a \
      final conditional subtraction; `[d]G` is `vg_ecdsa_p256_sign`'s fixed-base comb of 7-bit \
      signed digits from the 37 tables of `[m 2^(7j)]G` (`m = 1 … 64`) in the static \
      `VG_P256_COMB`, each entry selected in constant time by loading the whole table, with no \
      doublings; and `Z⁻¹` is by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 divsteps in all, enough for \
      256-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.EcKey.AArch64.publicKeyP256
    contract := Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.EcKey.AArch64.pk_verified h.law (Proof.P256.combOk7 h.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.P256.AArch64.EcP256
