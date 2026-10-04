import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.Arm.Derive.Verified

/-! # Argon2 (RFC 9106) on ARMv7 -/

namespace VG.Artifacts.Argon2.Arm

def artifacts : List Artifact := [
  { Spec.Argon2.compressApi with
    target := Arm.target
    doc := Spec.Argon2.compressApi.doc
    code := Impl.Argon2.Arm.compress
    contract := Spec.Argon2.compressContract Arm.abi
    stack := 0
    verified := Proof.Argon2.Arm.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Argon2.hPrimeApi with
    target := Arm.target
    doc := Spec.Argon2.hPrimeApi.doc
    code := Impl.Argon2.Arm.HPrime.code
    contract := Spec.Argon2.hPrimeContract Arm.abi 32
    stack := 32
    verified := Proof.Argon2.Arm.HPrime.hPrimeShared_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Argon2.deriveApi with
    target := Arm.target
    doc := Spec.Argon2.deriveApi.doc
    code := Impl.Argon2.Arm.Derive.derive
    contract := Spec.Argon2.deriveContract Arm.abi 240
    stack := 240
    verified := Proof.Argon2.Arm.Derive.deriveShared_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Argon2.Arm
