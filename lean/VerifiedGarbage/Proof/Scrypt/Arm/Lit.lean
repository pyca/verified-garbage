module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
meta import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# scrypt on Arm: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.Arm.salsa
materialize_code Impl.Scrypt.Arm.blockMix
materialize_code Impl.Scrypt.Arm.roMix

end VG
