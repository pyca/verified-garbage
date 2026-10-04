import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Verified

/-! # ECDSA over P-256 (FIPS 186-5) on AArch64 -/

namespace VG.Artifacts.EcdsaP256.AArch64

def artifacts : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19` and `x20`) in `scratch`. Field elements and scalars are four 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and \
      `umulh` and the multiplicand's words in registers; modulo `p`, `p ≡ -1 (mod 2⁶⁴)`, so each \
      step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts and one product) with a final \
      conditional subtraction. `[k]G` is a double-and-add ladder over all 256 bits of `k`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and doubling \
      and a masked selection for each bit; the inversions modulo `p` and `n` are Fermat's, by \
      square-and-always-multiply over the bits of `p - 2` and `n - 2`. The signature (or zeros) is \
      selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.AArch64.signP256
    contract := Spec.Ecdsa.P256.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.sign_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P256.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p256`'s checks of the public key: it \
      saves the callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements and \
      scalars are four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and `umulh` and the multiplicand's words in registers; \
      modulo `p`, `p ≡ -1 (mod 2⁶⁴)`, so each step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts \
      and one product) with a final conditional subtraction. The key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation), and the second \
      ladder multiplies the key's point if it is valid, else `G`, so it always runs on a point of \
      the curve. `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's, by square-and-always-multiply; `[u]G` \
      and `[v]Q` are double-and-add ladders over all 256 bits of `u` and `v`, with the complete \
      addition formulas of Renes, Costello and Batina, which also add the two. The result is the \
      conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point at \
      infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, \
      although the contract would let every input affect it."])
    code := Impl.Ecdsa.Verify.AArch64.verifyP256
    contract := Spec.Ecdsa.P256.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.verify_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP256.AArch64
