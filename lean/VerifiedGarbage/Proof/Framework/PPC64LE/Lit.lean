module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# PPC64LE code as literals

The instances `materialize_code` needs to write this ISA's code as a literal
(`Proof/Framework/Lit.lean`); `Reg`'s is in `Taint.lean`.
-/

@[expose] public section

namespace VG.PPC64LE

deriving instance Lean.ToExpr for Size
deriving instance Lean.ToExpr for LogicOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.PPC64LE
