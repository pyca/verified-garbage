module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86.PointBrainpoolP384r1
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.BrainpoolP384r1
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384

/-!
# brainpoolP384r1's point addition and doubling on x86 (32-bit)

`vg_brainpoolp384r1_point_add` and `vg_brainpoolp384r1_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
brainpoolP384r1's prime. A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law
`h`, the variant `Variants/BrainpoolP384r1/X86/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86.PointBrainpoolP384r1

open VG.Proof.Weierstrass.X86.Point VG.Proof.Weierstrass.Point

/-- How the functions work. -/
def notes : List String := ["The function saves `ebx` in its own working space, and computes \
  Renes, Costello and Batina's 40 steps by calls of `vg_brainpoolp384r1_mul_mod_p`, `vg_brainpoolp384r1_add_mod_p` and \
  `vg_brainpoolp384r1_sub_mod_p` on fixed offsets of `ws`, loading `ws` from its argument into `ebx` before \
  each call and pushing it and the offsets as the callee's arguments. It writes no register but \
  `eax`, `ecx` and `edx` (and `ebx`, which it restores)."]

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Weierstrass.Point.brainpoolp384r1.addApi.artifact X86.target {
    notes := notes
    code := Impl.Weierstrass.X86.Point.pointAdd Spec.Weierstrass.Point.brainpoolp384r1
    stack := 20
    verified := brainpoolp384r1_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.brainpoolp384r1.doubleApi.artifact X86.target {
    notes := notes
    code := Impl.Weierstrass.X86.Point.pointDouble Spec.Weierstrass.Point.brainpoolp384r1
    stack := 20
    verified := brainpoolp384r1_double_verified (fermat_of_law h.law) }]

end VG.Generic.BrainpoolP384r1.X86.PointBrainpoolP384r1
