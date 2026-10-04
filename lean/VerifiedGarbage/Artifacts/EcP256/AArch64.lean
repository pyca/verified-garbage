import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
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
      final conditional subtraction; `[d]G` is a double-and-add ladder over all 256 bits of `d`, \
      with the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling and a masked selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."])
    code := Impl.EcKey.AArch64.publicKeyP256
    contract := Spec.EcKey.P256.inst.publicKeyContract AArch64.abi
    verified := Proof.EcKey.AArch64.pk_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcP256.AArch64
