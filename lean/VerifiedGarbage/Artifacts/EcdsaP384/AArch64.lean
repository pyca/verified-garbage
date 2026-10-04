import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P384.Curve
import VerifiedGarbage.Proof.P384.Comb
import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Verified

/-! # ECDSA over P-384 (FIPS 186-5) on AArch64 -/

namespace VG.Artifacts.EcdsaP384.AArch64

def artifacts : List Artifact := [
  { Spec.Ecdsa.P384.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P384.signApi.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19` and `x20`) in `scratch`. Field elements and scalars are six 64-bit words in \
      Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and \
      `umulh`, four of the multiplicand's words in registers and the other two loaded for each \
      word of the multiplier; each reduction step multiplies the accumulator's low word by \
      `-m⁻¹ mod 2⁶⁴` and adds that multiple of the modulus) with a final conditional \
      subtraction. `[k]G` is a fixed-base comb: the 96 nibbles `k_j` of `k` as digits \
      `k_j - 8` from `-8` to `7`, `[k]G = [8 Σ 16^j]G + Σ [(k_j - 8) 16^j]G` from 96 constant \
      tables of `[m 16^j]G` (`m = 1 … 8`), each entry selected in constant time from immediates by \
      masks of the digit's magnitude and negated by a mask of its sign, and added by the complete \
      addition formulas of Renes, Costello and Batina for `a = -3` (Algorithm 4: 12 products and \
      2 by `b`); the inversions modulo `p` and `n` are \
      Fermat's, by chains of sliding 4-bit windows over `p - 2` and `n - 2`, fixed by the code \
      (squarings and products by a table of odd powers). The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.AArch64.signP384
    contract := Spec.Ecdsa.P384.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.P384.sign_verified Proof.P384.law Proof.P384.combOk
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Ecdsa.P384.verifyApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P384.verifyApi.doc (notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, comb and inversions, with `vg_ecdh_p384`'s checks of the public key: it \
      saves the callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements and \
      scalars are six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and `umulh`, four of the multiplicand's words in registers \
      and the other two loaded for each word of the multiplier; each reduction step multiplies \
      the accumulator's low word by `-m⁻¹ mod 2⁶⁴` and adds that multiple of the modulus) with a \
      final conditional subtraction. The key is checked without branches \
      (its first byte, both coordinates below `p`, and the curve's equation), and `[v]Q` is \
      computed for the key's point if it is valid, else `G`, so always on a point of the curve. \
      `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's, by the signature's chains; `[u]G` is the \
      signature's comb over the nibbles of `u`, and `[v]Q` `vg_ecdh_p384`'s signed 4-bit windows \
      (97 digits of `v + 8 Σ_{j<97} 16^j`, four doublings in Jacobian coordinates and a \
      constant-time selection from a \
      table of `[1 … 8]Q` each), with the complete formulas of Renes, Costello and Batina for \
      `a = -3`, which also add the two. The result is the conjunction of the checks (the key, \
      `r` and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a mask, so the time \
      depends only on the pointers, although the contract would let every input affect it."])
    code := Impl.Ecdsa.Verify.AArch64.verifyP384
    contract := Spec.Ecdsa.P384.inst.verifyContract AArch64.abi
    verified := Proof.Ecdsa.Verify.AArch64.P384.verify_verified Proof.P384.law Proof.P384.combOk
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP384.AArch64
