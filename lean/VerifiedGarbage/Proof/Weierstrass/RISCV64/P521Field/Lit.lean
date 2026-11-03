module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-521's prime `p = 2⁵²¹ - 1` on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.P521Field.mulFn
materialize_code Impl.Weierstrass.RISCV64.P521Field.addFn
materialize_code Impl.Weierstrass.RISCV64.P521Field.subFn
materialize_code Impl.Weierstrass.RISCV64.P521Field.mulFnA
materialize_code Impl.Weierstrass.RISCV64.P521Field.addFnA
materialize_code Impl.Weierstrass.RISCV64.P521Field.subFnA

theorem Impl.Weierstrass.RISCV64.P521Field.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Field.addFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Field.subFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.subFn.noFrames = true := by lit_decide

theorem Impl.Weierstrass.RISCV64.P521Field.mulFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.mulFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Field.addFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.addFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Field.subFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Field.subFnA.noFrames = true := by lit_decide

end VG
