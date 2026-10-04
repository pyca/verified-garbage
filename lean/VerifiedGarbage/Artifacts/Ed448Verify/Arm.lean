import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified
import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification on ARMv7

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_verify_equation` is passed to the caller's here, so that only
this file imports it, with the reference computations' agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

namespace VG.Artifacts.Ed448Verify.Arm

def artifacts : List Artifact := [
  { Spec.Ed448.verifyApi with
    target := Arm.target
    doc := Spec.Ed448.verifyApi.doc (notes := ["Uses baseline integer instructions. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, with the Keccak state and the sponge functions' \
      working space in `scratch`) into the frame, reduces the hash modulo L there with \
      `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s result. The frame \
      (the hash and k) is not cleared: verification has no secrets."])
    code := Impl.Ed448.Arm.Verify.code
    contract := Spec.Ed448.verifyContract Arm.abi 280
    stack := 280
    verified := Proof.Ed448.Arm.Verify.verify_verified
      (Proof.Ed448.Arm.verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
      Proof.Ed448.Arm.verifyEquation_ct
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed448Verify.Arm
