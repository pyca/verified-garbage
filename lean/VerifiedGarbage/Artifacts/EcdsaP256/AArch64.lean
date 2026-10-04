import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.Comb
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
      conditional subtraction. `[k]G` is a fixed-base comb: the 64 nibbles `k_j` of `k` as digits \
      `k_j - 8` from `-8` to `7`, `[k]G = [8 Σ 16^j]G + Σ [(k_j - 8) 16^j]G` from 64 constant \
      tables of `[m 16^j]G` (`m = 1 … 8`), each entry selected in constant time from immediates by \
      masks of the digit's magnitude and negated by a mask of its sign, and added by the complete \
      addition formulas of Renes, Costello and Batina; the inversions modulo `p` and `n` are \
      Fermat's, by chains of sliding 4-bit windows over `p - 2` and `n - 2`, fixed by the code \
      (squarings and products by a table of odd powers). The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.AArch64.signP256
    contract := Spec.Ecdsa.P256.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.sign_verified Proof.P256.law Proof.P256.combOk
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P256.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s setup, \
      field arithmetic, comb and inversions, with `vg_ecdh_p256`'s checks of the public key: it \
      saves the callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements and \
      scalars are four 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and `umulh` and the multiplicand's words in registers; \
      modulo `p`, `p ≡ -1 (mod 2⁶⁴)`, so each step adds `t₀ (p + 1) / 2⁶⁴`, which takes two shifts \
      and one product) with a final conditional subtraction. The key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation), and `[v]Q` is \
      computed for the key's point if it is valid, else `G`, so always on a point of the curve. \
      `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's, by the signature's chains; `[u]G` is the \
      signature's comb over the nibbles of `u`, and `[v]Q` `vg_ecdh_p256`'s signed 4-bit windows \
      (65 digits of `v + 8 Σ_{j<65} 16^j`, four doublings and a constant-time selection from a \
      table of `[1 … 8]Q` each), with the complete addition formulas of Renes, Costello and \
      Batina, which also add the two. The result is the conjunction of the checks (the key, `r` and `s` in `[1, \
      n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a mask, so the time \
      depends only on the pointers, although the contract would let every input affect it."])
    code := Impl.Ecdsa.Verify.AArch64.verifyP256
    contract := Spec.Ecdsa.P256.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.verify_verified Proof.P256.law Proof.P256.combOk
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP256.AArch64
