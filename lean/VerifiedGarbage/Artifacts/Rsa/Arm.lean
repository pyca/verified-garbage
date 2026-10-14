module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified

/-! # RSA public precomputation on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rsa.Arm
open VG.Arm

def artifacts : List Artifact := [
  { Spec.Rsa.publicPrecomputeApi with
    target := target
    doc := Spec.Rsa.publicPrecomputeApi.doc
      (notes := ["Baseline ARMv7: validates the modulus, imports it using 32-bit limbs, computes \
        the full 64-bit Montgomery inverse with paired native words, and computes R² mod n \
        with a fixed number of modular doublings. Writes the shared 64-bit precomputation \
        format and clears the output for an invalid modulus. Uses a 56-byte AAPCS stack frame."])
    code := Impl.Bignum.Arm.PcFn.code
    contract := Spec.Rsa.publicPrecomputeContract abi 56
    stack := 56
    verified := Proof.Bignum.Arm.precompute_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rsa.Arm
