module

public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.X448.Arm.FnLit
public import VerifiedGarbage.Impl.X448.Arm.Base
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Impl.X448.Arm.Base
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# X448 of the base point on ARMv7: the code as a literal

The kernel checks the literal once.

The constant-time analysis, from the arguments alone, reads neither the
offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`x448BaseErased`: there the field operations on the working space's slots
are the same code, which its literal shares, and the kernel analyses each
once from the same taint rather than every copy.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.x448Base

/-- `x448Base` without its offsets. -/
def Proof.X448.Arm.x448BaseErased : Prog Arm.isa := Arm.Code.eraseOff Impl.X448.Arm.x448Base

materialize_code Proof.X448.Arm.x448BaseErased

end VG
