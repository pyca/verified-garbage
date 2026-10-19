module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Proof.Weierstrass.X86.PointBrainpoolP256r1
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384

/-!
# brainpoolP256r1's point addition and doubling on x86 (32-bit)

`vg_brainpoolp256r1_point_add` and `vg_brainpoolp256r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP256r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law
`h`, the variant `Variants/BrainpoolP256r1/X86/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.X86.PointBrainpoolP256r1

open VG.Proof.Weierstrass.X86.Point VG.Proof.Weierstrass.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `ebx` in its own working space, and computes \
  Renes, Costello and Batina's 40 steps by calls of `vg_brainpoolp256r1_mul_mod_p`, `vg_brainpoolp256r1_add_mod_p` and \
  `vg_brainpoolp256r1_sub_mod_p` on fixed offsets of `ws`, loading `ws` from its argument into `ebx` before \
  each call and pushing it and the offsets as the callee's arguments. It writes no register but \
  `eax`, `ecx` and `edx` (and `ebx`, which it restores)."]

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp256r1.addApi.artifact X86.target {
    notes := notes
    code := Impl.Weierstrass.X86.Point.pointAdd Spec.Weierstrass.Point.brainpoolp256r1
    stack := 20
    verified := brainpoolp256r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp256r1.doubleApi.artifact X86.target {
    notes := notes
    code := Impl.Weierstrass.X86.Point.pointDouble Spec.Weierstrass.Point.brainpoolp256r1
    stack := 20
    verified := brainpoolp256r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP256r1.X86.PointBrainpoolP256r1
