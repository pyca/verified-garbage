import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified

/-! # ECDSA over P-256 (FIPS 186-5) on AArch64 -/

namespace VG.Artifacts.EcdsaP256.AArch64

def artifacts : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := AArch64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19` and `x20`) in `scratch`. Field elements and scalars are four 64-bit words \
      in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with \
      `mul` and `umulh`) with a final conditional subtraction. `[k]G` is a double-and-add \
      ladder over all 256 bits of `k`, with the complete addition formulas of Renes, Costello \
      and Batina for every addition and doubling and a masked selection for each bit; the \
      inversions modulo `p` and `n` are Fermat's, by square-and-always-multiply over the bits \
      of `p - 2` and `n - 2`. The signature (or zeros) is selected by a mask, so the time \
      depends only on the pointers."])
    code := Impl.Ecdsa.AArch64.signP256
    contract := Spec.Ecdsa.P256.inst.signContract AArch64.abi
    verified := Proof.Ecdsa.AArch64.sign_verified Proof.P256.law
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.EcdsaP256.AArch64
