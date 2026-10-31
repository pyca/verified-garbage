module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P192
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P224
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P256
public import VerifiedGarbage.Proof.Weierstrass.X86.PointLit.P384
public import VerifiedGarbage.Proof.Weierstrass.X86.PointCurves
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Mont.X86.Chain
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.P256Red
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.SparseShift
public import VerifiedGarbage.Proof.Mont.X86.SparseStep
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
public import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.PointVerified
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Fold

/-!
# P-224's point addition and doubling on x86 (32-bit)

`vg_p224_point_add` and `vg_p224_point_double`
(`Spec/Weierstrass/Point.lean`), calling the Montgomery functions of
P-224's prime. A generic file (see `TCB/Emit.lean`) over P-224's group law
`h`, the variant `Variants/P224/X86/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.P224.X86.PointP224

open VG.Proof.Weierstrass.X86.Point VG.Proof.Weierstrass.Point

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Point.p224.addApi.artifact X86.target {
    code := Impl.Weierstrass.X86.Point.pointAdd Spec.Weierstrass.Point.p224
    stack := 20
    verified := p224_add_verified (fermat_of_law h.law) },
  Spec.Weierstrass.Point.p224.doubleApi.artifact X86.target {
    code := Impl.Weierstrass.X86.Point.pointDouble Spec.Weierstrass.Point.p224
    stack := 20
    verified := p224_double_verified (fermat_of_law h.law) }]

end VG.Generic.P224.X86.PointP224
