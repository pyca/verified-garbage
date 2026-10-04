import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Ed448.Facts

/-!
# Ed448 verification on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_verify_equation` is passed to the caller's here, so that only
this file imports it, with the reference computations' agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

namespace VG.Artifacts.Ed448Verify.X86

open VG.X86

theorem equation_ok :
    Proof.Ed448.X86.CalleeOk Proof.Ed448.X86.verifyEquationLocal Impl.Ed448.X86.verifyEquation :=
  ⟨Proof.Ed448.X86.verifyEquation_ok Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok,
    Proof.Ed448.X86.verifyEquation_ct, NoSp.of_all (by lit_decide), by lit_decide⟩

def artifacts : List Artifact := [
  { Spec.Ed448.verifyApi with
    target := X86.target
    doc := Spec.Ed448.verifyApi.doc (notes := ["Uses baseline integer instructions. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, with the Keccak state and the sponge functions' \
      working space in `scratch`) into the frame, reduces the hash modulo L there with \
      `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s result. The frame \
      (the hash and k) is not cleared: verification has no secrets."])
    code := Impl.Ed448.X86.Verify.code Impl.Ed448.X86.verifyEquation
    contract := Spec.Ed448.verifyContract X86.abi 280
    stack := 280
    verified := Proof.Ed448.X86.Verify.verify_verified equation_ok
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448Verify.X86
