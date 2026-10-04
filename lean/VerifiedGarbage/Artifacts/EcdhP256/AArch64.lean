import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.Verified

/-! # ECDH over P-256 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP256.AArch64

def artifacts : List Artifact := [
  { Spec.Ecdh.P256.exchangeApi with
    target := AArch64.target
    doc := Spec.Ecdh.P256.exchangeApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers it uses (`x19` and `x20`) in `scratch`; field elements are four \
      64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and `umulh`) with a final conditional subtraction. The peer's key is \
      checked without branches (its first byte, both coordinates below `p`, and the curve's \
      equation), and the ladder multiplies the peer's point if it is valid, else `G`, so it \
      always runs on a point of the curve. `[d]P` is a double-and-add ladder over all 256 bits \
      of `d`, with the complete addition formulas of Renes, Costello and Batina and a masked \
      selection for each bit; `Z⁻¹` is Fermat's, by square-and-always-multiply. The result (or \
      zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so the time \
      depends only on the pointers."])
    code := Impl.Ecdh.AArch64.exchangeP256
    contract := Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst AArch64.abi
    verified := Proof.Ecdh.AArch64.ecdh_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdhP256.AArch64
