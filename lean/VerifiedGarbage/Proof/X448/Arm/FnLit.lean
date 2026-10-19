module

public import VerifiedGarbage.Impl.X448.Arm
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.X448.Arm
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

/-!
# X448 on ARMv7: the field functions as literals

The callers' literals refer to these (`materialize_code`), so the kernel
builds each function's code once.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.mulFn
materialize_code Impl.X448.Arm.addFn
materialize_code Impl.X448.Arm.subFn
materialize_code Impl.X448.Arm.mulA24Fn

end VG
