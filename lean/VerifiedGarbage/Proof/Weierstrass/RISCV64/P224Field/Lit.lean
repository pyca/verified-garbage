module

public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-224's `p` and `n` on RISC-V: the code as literals

The six functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.p224MulP
materialize_code Impl.Ecdsa.RISCV64.p224AddP
materialize_code Impl.Ecdsa.RISCV64.p224SubP
materialize_code Impl.Ecdsa.RISCV64.p224MulN
materialize_code Impl.Ecdsa.RISCV64.p224AddN
materialize_code Impl.Ecdsa.RISCV64.p224SubN

theorem Impl.Ecdsa.RISCV64.p224MulP_noFrames : Impl.Ecdsa.RISCV64.p224MulP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p224AddP_noFrames : Impl.Ecdsa.RISCV64.p224AddP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p224SubP_noFrames : Impl.Ecdsa.RISCV64.p224SubP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p224MulN_noFrames : Impl.Ecdsa.RISCV64.p224MulN.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p224AddN_noFrames : Impl.Ecdsa.RISCV64.p224AddN.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p224SubN_noFrames : Impl.Ecdsa.RISCV64.p224SubN.noFrames = true := by lit_decide

end VG
