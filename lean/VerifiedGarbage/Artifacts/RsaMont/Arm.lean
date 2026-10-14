module

public import VerifiedGarbage.Proof.Bignum.Arm.MontVerified

/-! # Montgomery multiplication in the shared RSA workspace on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaMont.Arm
open VG.Arm

def artifacts : List Artifact := [
  { Spec.Rsa.Mont.mulApi with
    target := target
    doc := Spec.Rsa.Mont.mulApi.doc
      (notes := ["Baseline ARMv7: coarsely integrated operand scanning with two 32-bit limbs per \
        64-bit workspace word. Wide products use four 16-bit partial products with MUL. \
        The accumulator is array 2; array 3 holds loop metadata and the final subtraction. \
        A mask selects the canonical result. Saves and restores callee-saved registers in \
        36 bytes of stack. The workspace layout and precomputed inverse are unchanged."])
    code := Impl.Bignum.Arm.MontFn.mul
    contract := Spec.Rsa.Mont.mulContract abi 36
    stack := 36
    verified := Proof.Bignum.Arm.mont_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.RsaMont.Arm
