module

public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# RISC-V code as literals

The instances `materialize_code` needs to write this ISA's code as a literal
(`Proof/Framework/Lit.lean`); `Reg`'s is in `Taint.lean`.
-/

@[expose] public section

namespace VG.RISCV64

deriving instance Lean.ToExpr for Size
deriving instance Lean.ToExpr for Width
deriving instance Lean.ToExpr for LogicOp
deriving instance Lean.ToExpr for ShiftOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.RISCV64
