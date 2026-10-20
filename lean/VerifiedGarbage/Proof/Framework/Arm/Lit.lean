module

public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target

/-!
# Shift code as literals

The instances `materialize_code` needs to write this ISA's code as a literal
(`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Arm

deriving instance Lean.ToExpr for Shift
deriving instance Lean.ToExpr for Op2
deriving instance Lean.ToExpr for DpOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.Arm
