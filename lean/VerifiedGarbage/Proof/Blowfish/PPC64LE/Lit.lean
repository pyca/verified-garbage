module

public import VerifiedGarbage.Impl.Blowfish.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it. -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.PPC64LE.encrypt
materialize_code Impl.Blowfish.PPC64LE.decrypt

end VG
