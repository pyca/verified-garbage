module

public import VerifiedGarbage.Impl.Rc2.Arm.Block
meta import VerifiedGarbage.Impl.Rc2.Arm.Block
public import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Impl.Rc2.Arm

open VG.Arm

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

materialize_flat_code expandKey

end VG.Impl.Rc2.Arm
