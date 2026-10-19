module

public import VerifiedGarbage.Impl.Ed25519.Arm.Power
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ed25519.Arm.Power
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

/-! The functions of point arithmetic and the inversion chain, and their
bodies, as literals (`materialize_code`), which their own constant-time
checks and the literals of the code that calls them read rather than build
each field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code chain250
materialize_code Point16.addFn
materialize_code Point16.doubleFn
materialize_code pow250Fn

end VG.Impl.Ed25519.Arm
