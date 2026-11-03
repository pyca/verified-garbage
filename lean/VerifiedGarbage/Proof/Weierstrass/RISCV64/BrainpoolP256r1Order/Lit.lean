module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP256r1Order
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP256r1Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo brainpoolp256r1's order on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFnA
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFnA
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFnA

theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFn.noFrames = true := by lit_decide

theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.mulFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.addFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Order.subFnA.noFrames = true := by lit_decide

end VG
