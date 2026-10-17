module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.Arm
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# ECDSA verification over brainpoolP512r1 on 32-bit ARM: the code as a literal

As for the signature (`Proof/Ecdsa/Arm/Lit.lean`): the literal of the code is
checked once here, rather than rebuilt in every check that evaluates it.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.Verify.Arm.verifyBrainpoolP512r1

end VG
