import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.X448.Arm.FnLit
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase

/-!
# Ed448 base-point multiplication on ARMv7: the code as a literal

The kernel checks the literal once.

The constant-time analysis, from the arguments alone, reads neither the
offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`scalarBaseErased`: there the field operations on the working space's slots
are the same code, which its literal shares, and the kernel analyses each
once from the same taint rather than every copy.
-/

namespace VG

materialize_code Impl.Ed448.Arm.scalarBase

/-- `scalarBase` without its offsets. -/
def Proof.Ed448.Arm.scalarBaseErased : Prog Arm.isa := Arm.Code.eraseOff Impl.Ed448.Arm.scalarBase

materialize_code Proof.Ed448.Arm.scalarBaseErased

end VG
