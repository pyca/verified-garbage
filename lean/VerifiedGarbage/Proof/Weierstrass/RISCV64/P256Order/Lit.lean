module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-256's order on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.P256Order.mulFn
materialize_code Impl.Weierstrass.RISCV64.P256Order.addFn
materialize_code Impl.Weierstrass.RISCV64.P256Order.subFn

theorem Impl.Weierstrass.RISCV64.P256Order.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.P256Order.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P256Order.addFn_noFrames :
    Impl.Weierstrass.RISCV64.P256Order.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P256Order.subFn_noFrames :
    Impl.Weierstrass.RISCV64.P256Order.subFn.noFrames = true := by lit_decide

end VG
