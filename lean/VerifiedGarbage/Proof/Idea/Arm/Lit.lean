module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.Arm
meta import VerifiedGarbage.Impl.Idea.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # Literal IDEA programs for kernel-evaluated checks (ARMv7) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.Arm.expandKey
materialize_code Impl.Idea.Arm.invertKey
materialize_code Impl.Idea.Arm.ecb

end VG
