module

import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.Arm
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Idea.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

/-! # Literal IDEA programs for kernel-evaluated checks (ARMv7) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.Arm.expandKey
materialize_code Impl.Idea.Arm.invertKey
materialize_code Impl.Idea.Arm.ecb

end VG
