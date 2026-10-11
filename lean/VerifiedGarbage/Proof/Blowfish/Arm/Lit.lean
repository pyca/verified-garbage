import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it, the initial schedule's immediates included. -/

namespace VG

materialize_code Impl.Blowfish.Arm.encrypt
materialize_code Impl.Blowfish.Arm.decrypt


end VG
