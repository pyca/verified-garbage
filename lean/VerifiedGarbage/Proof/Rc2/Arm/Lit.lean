module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Rc2.Arm.Block
meta import VerifiedGarbage.Impl.Rc2.Arm.Block
public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
meta import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

materialize_flat_code expandKey

end VG.Impl.Rc2.Arm
