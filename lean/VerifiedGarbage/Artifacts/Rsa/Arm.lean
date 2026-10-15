module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified

/-! # RSA operations on ARMv7 -/

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
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.publicCheckedApi with
    target := target
    doc := Spec.Rsa.publicCheckedApi.doc
      (notes := ["Baseline ARMv7: validates the public modulus and exponent, computes Montgomery \
        precomputation, and performs binary exponentiation using native 32-bit limbs. The input \
        is secret: the input-range comparison is retained as a mask, and out-of-range inputs \
        follow the same arithmetic path before branchless output clearing. Uses a 56-byte \
        AAPCS stack frame."])
    code := Impl.Bignum.Arm.PublicFn.code
    contract := Spec.Rsa.publicCheckedContract abi 56
    stack := 56
    verified := Proof.Bignum.Arm.public_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.publicPrecomputedCheckedApi with
    target := target
    doc := Spec.Rsa.publicPrecomputedCheckedApi.doc
      (notes := ["Baseline ARMv7: imports the shared packed modulus and R² format, validates the \
        public arithmetic preconditions, and computes only the Montgomery inverse before binary \
        exponentiation. Input acceptance and output clearing are branchless. Uses a 56-byte AAPCS \
        stack frame."])
    code := Impl.Bignum.Arm.PdFn.code
    contract := Spec.Rsa.publicPrecomputedCheckedContract abi 56
    stack := 56
    verified := Proof.Bignum.Arm.pd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rsa.privateCrtApi with
    target := target
    doc := Spec.Rsa.privateCrtApi.doc
      (notes := ["Baseline ARMv7: fixed-schedule private exponentiation with native 32-bit limbs, \
        signed CRT coefficient reduction, and wide reconstruction. Secret input and key checks \
        accumulate a mask; rejected factors are sanitized and rejected outputs are cleared without \
        secret-dependent branches. Both factors use the public modulus width. Uses the shared \
        scratch contract and a 56-byte AAPCS stack frame."])
    code := Impl.Bignum.Arm.CrtFn.code
    contract := Spec.Rsa.privateCrtContract abi 56
    stack := 56
    verified := Proof.Bignum.Arm.crt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rsa.Arm
