module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! Literal code keeps the audits that evaluate it (constant time, `spSafe`)
from rebuilding it. -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.PPC64LE.encryptBlock
materialize_code Impl.Rc2.PPC64LE.decryptBlock

end VG
