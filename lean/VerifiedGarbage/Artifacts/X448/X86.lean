module

public import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Proof.X448.X86.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact X86.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are twenty-eight 16-bit limbs in `scratch`; the field \
      arithmetic is by calls of `vg_gf448_r16_mul`, `vg_gf448_r16_add`, `vg_gf448_r16_sub` and \
      `vg_gf448_r16_mul_a24`. Inversion uses an addition chain for `p - 2`."]
    code := Impl.X448.X86.x448
    stack := 20
    verified := Proof.X448.X86.x448_verified }]

end VG.Artifacts.X448.X86
