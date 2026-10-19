module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyEquationOk
public import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-!
# Ed448 verification on x86 (32-bit)

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_verify_equation` is passed to the caller's here, so that only
this file imports it, with the reference computations' agreement with the
specification (`Proof/Ed448/Facts.lean`).
-/

@[expose] public section

namespace VG.Artifacts.Ed448Verify.X86

open VG.X86

def artifacts : List Artifact := [
  Spec.Ed448.verifyApi.artifact X86.target {
    notes := ["Uses baseline integer instructions. Returns 0 \
      at once for a context of 256 bytes or more. Otherwise writes the first ten bytes of \
      dom4(0, C) into a stack frame, hashes them, the context, R, the public key and the \
      message with `vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch` and \
      `vg_keccak_squeeze_scratch` (SHAKE256, with the Keccak state and the sponge functions' \
      working space in `scratch`) into the frame, reduces the hash modulo L there with \
      `vg_ed448_scalar_reduce`, and returns `vg_ed448_verify_equation`'s result. The frame \
      (the hash and k) is not cleared: verification has no secrets."]
    code := Impl.Ed448.X86.Verify.code Impl.Ed448.X86.verifyEquation
    stack := 280
    verified := Proof.Ed448.X86.Verify.verify_verified Proof.Ed448.X86.verifyEquation_calleeOk }]

end VG.Artifacts.Ed448Verify.X86
