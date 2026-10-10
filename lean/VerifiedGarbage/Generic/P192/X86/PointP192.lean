import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves

/-!
# P-192's point addition and doubling on x86 (32-bit)

`vg_p192_point_add` and `vg_p192_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-192's prime. A generic file (see `TCB/Emit.lean`) over P-192's group law
`h`, the variant `Variants/P192/X86/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

namespace VG.Generic.P192.X86.PointP192

open VG.Proof.Weierstrass.X86.Point VG.Proof.Weierstrass.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `ebx` in its own working space, and computes \
  Renes, Costello and Batina's 40 steps by calls of `vg_p192_mul_mod_p`, `vg_p192_add_mod_p` and \
  `vg_p192_sub_mod_p` on fixed offsets of `ws`, loading `ws` from its argument into `ebx` before \
  each call and pushing it and the offsets as the callee's arguments. It writes no register but \
  `eax`, `ecx` and `edx` (and `ebx`, which it restores)."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  { Spec.Weierstrass.Point.p192.addApi with
    target := X86.target
    doc := Spec.Weierstrass.Point.p192.addApi.doc (notes := notes)
    code := Impl.Weierstrass.X86.Point.pointAdd Spec.Weierstrass.Point.p192
    contract := Spec.Weierstrass.Point.p192.addContract X86.abi 20
    stack := 20
    verified := p192_add_verified (fermat_of_law h.law)
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Weierstrass.Point.p192.doubleApi with
    target := X86.target
    doc := Spec.Weierstrass.Point.p192.doubleApi.doc (notes := notes)
    code := Impl.Weierstrass.X86.Point.pointDouble Spec.Weierstrass.Point.p192
    contract := Spec.Weierstrass.Point.p192.doubleContract X86.abi 20
    stack := 20
    verified := p192_double_verified (fermat_of_law h.law)
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.P192.X86.PointP192
