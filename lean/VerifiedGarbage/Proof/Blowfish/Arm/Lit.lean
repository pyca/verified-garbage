module

public import VerifiedGarbage.Impl.Blowfish.Arm
meta import VerifiedGarbage.Impl.Blowfish.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it. -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.Arm.encrypt
materialize_code Impl.Blowfish.Arm.decrypt


end VG
