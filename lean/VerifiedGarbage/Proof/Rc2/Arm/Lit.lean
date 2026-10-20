module

public import VerifiedGarbage.Impl.Rc2.Arm.Block
public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.Arm.Block
meta import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

materialize_flat_code expandKey

end VG.Impl.Rc2.Arm
