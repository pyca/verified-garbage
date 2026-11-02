module

public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-192's `p` and `n` on RISC-V: the code as literals

The six functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Ecdsa.RISCV64.p192MulP
materialize_code Impl.Ecdsa.RISCV64.p192AddP
materialize_code Impl.Ecdsa.RISCV64.p192SubP
materialize_code Impl.Ecdsa.RISCV64.p192MulN
materialize_code Impl.Ecdsa.RISCV64.p192AddN
materialize_code Impl.Ecdsa.RISCV64.p192SubN

theorem Impl.Ecdsa.RISCV64.p192MulP_noFrames : Impl.Ecdsa.RISCV64.p192MulP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p192AddP_noFrames : Impl.Ecdsa.RISCV64.p192AddP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p192SubP_noFrames : Impl.Ecdsa.RISCV64.p192SubP.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p192MulN_noFrames : Impl.Ecdsa.RISCV64.p192MulN.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p192AddN_noFrames : Impl.Ecdsa.RISCV64.p192AddN.noFrames = true := by lit_decide
theorem Impl.Ecdsa.RISCV64.p192SubN_noFrames : Impl.Ecdsa.RISCV64.p192SubN.noFrames = true := by lit_decide

end VG
