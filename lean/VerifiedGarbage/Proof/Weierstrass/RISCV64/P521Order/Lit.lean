module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-521's order `n` on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.P521Order.mulFn
materialize_code Impl.Weierstrass.RISCV64.P521Order.addFn
materialize_code Impl.Weierstrass.RISCV64.P521Order.subFn
materialize_code Impl.Weierstrass.RISCV64.P521Order.mulFnA
materialize_code Impl.Weierstrass.RISCV64.P521Order.addFnA
materialize_code Impl.Weierstrass.RISCV64.P521Order.subFnA

theorem Impl.Weierstrass.RISCV64.P521Order.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Order.addFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Order.subFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.subFn.noFrames = true := by lit_decide

theorem Impl.Weierstrass.RISCV64.P521Order.mulFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.mulFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Order.addFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.addFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Order.subFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Order.subFnA.noFrames = true := by lit_decide

end VG
