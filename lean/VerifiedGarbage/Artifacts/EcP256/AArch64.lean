import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.EcKey.P256.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.Verified

/-! # P-256 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP256.AArch64

def artifacts : List Artifact := [
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
      doublings; and `Z⁻¹` is Fermat's, by \
      a chain of sliding 4-bit windows over `p - 2`, fixed by the code. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    consts := Impl.Ecdsa.AArch64.p256.combConsts
    code := Impl.EcKey.AArch64.publicKeyP256
    contract := Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts)
    verified := Proof.EcKey.AArch64.pk_verified Proof.P256.law (Proof.P256.combOk7 Proof.P256.law)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcP256.AArch64
