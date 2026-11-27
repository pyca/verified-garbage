module

public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.X448.Arm.FnLit
public import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed448 verification's equation on ARMv7: the code as literals

The kernel checks each literal once: the function's, and those of the parts
the constant-time proof analyses on their own (`Proof/Ed448/Arm/
VerifyVerified.lean`): what comes before `k`'s digits, the table of `-A`'s odd
multiples, a bit's doubling and additions in the loop over the bits of `S`
and the digits of `k`, and what comes after the loop.

The analysis of what comes before the loop, from the arguments alone, reads
neither the offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`vbeforeErased`: there the field operations on the working space's slots are
the same code, which its literal shares, and the kernel analyses each once
from the same taint rather than every copy.
-/

@[expose] public section

namespace VG

materialize_code Proof.Ed448.Arm.vbeforePlain := Impl.Ed448.Arm.vbefore false
materialize_code Proof.Ed448.Arm.vbeforeUmaal := Impl.Ed448.Arm.vbefore true
materialize_code Proof.Ed448.Arm.vtablePlain := Impl.Ed448.Arm.vtable false
materialize_code Proof.Ed448.Arm.vtableUmaal := Impl.Ed448.Arm.vtable true
materialize_code Proof.Ed448.Arm.vdoubleAddPlain := Impl.Ed448.Arm.vdoubleAdd false
materialize_code Proof.Ed448.Arm.vdoubleAddUmaal := Impl.Ed448.Arm.vdoubleAdd true
materialize_code Proof.Ed448.Arm.vafterPlain := Impl.Ed448.Arm.vafter false
materialize_code Proof.Ed448.Arm.vafterUmaal := Impl.Ed448.Arm.vafter true
materialize_code Proof.Ed448.Arm.verifyEquationPlain := Impl.Ed448.Arm.verifyEquation false
materialize_code Proof.Ed448.Arm.verifyEquationUmaal := Impl.Ed448.Arm.verifyEquation true

/-- `vbefore` without its offsets. -/
def Proof.Ed448.Arm.vbeforeErased : Prog Arm.isa :=
  Arm.Code.eraseOff (Impl.Ed448.Arm.vbefore false)

materialize_code Proof.Ed448.Arm.vbeforeErased

end VG
