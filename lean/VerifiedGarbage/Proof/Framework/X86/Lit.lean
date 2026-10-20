module

public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# x86 (32-bit) code as literals

The instances `materialize_code` needs to write x86 code as a literal
(`Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.X86

deriving instance Lean.ToExpr for MemOp
deriving instance Lean.ToExpr for Reg8
deriving instance Lean.ToExpr for Src
deriving instance Lean.ToExpr for AluOp
deriving instance Lean.ToExpr for ShiftOp
deriving instance Lean.ToExpr for XReg
deriving instance Lean.ToExpr for XBinOp
deriving instance Lean.ToExpr for XShiftOp
deriving instance Lean.ToExpr for XOp
deriving instance Lean.ToExpr for MReg
deriving instance Lean.ToExpr for MSrc
deriving instance Lean.ToExpr for MBinOp
deriving instance Lean.ToExpr for MShiftOp
deriving instance Lean.ToExpr for MOp
deriving instance Lean.ToExpr for Instr
deriving instance Lean.ToExpr for Cond

end VG.X86
