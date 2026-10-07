import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X448.X86
import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Proof.X448.X86.Lit

/-! # X448 (RFC 7748) on x86 (32-bit) -/

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := X86.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are twenty-eight 16-bit limbs in `scratch`; the field \
      arithmetic is by calls of `vg_gf448_r16_mul`, `vg_gf448_r16_add`, `vg_gf448_r16_sub` and \
      `vg_gf448_r16_mul_a24`. Inversion uses an addition chain for `p - 2`."])
    code := Impl.X448.X86.x448
    contract := Spec.X448.x448Contract X86.abi 20
    stack := 20
    verified := Proof.X448.X86.x448_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X448.X86
