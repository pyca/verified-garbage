module

public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
public import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
meta import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-!
# Ed448 verification's equation on ARMv7: the code as a literal

The kernel checks the literal once.

The constant-time analysis, from the arguments alone, reads neither the
offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`verifyEquationErased`: there the field operations on the working space's
slots (some 150 multiplications) are the same code, which its literal
shares, and the kernel analyses each once from the same taint rather than
every copy.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.Arm.verifyEquation

/-- `verifyEquation` without its offsets. -/
def Proof.Ed448.Arm.verifyEquationErased : Prog Arm.isa :=
  Arm.Code.eraseOff Impl.Ed448.Arm.verifyEquation

materialize_code Proof.Ed448.Arm.verifyEquationErased

end VG
