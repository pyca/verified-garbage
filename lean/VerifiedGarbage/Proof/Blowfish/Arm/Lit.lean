module

public import VerifiedGarbage.Impl.Blowfish.Arm
meta import VerifiedGarbage.Impl.Blowfish.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it, the initial schedule's immediates included. -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.Arm.encrypt
materialize_code Impl.Blowfish.Arm.decrypt


end VG
