module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo brainpoolP512r1's prime on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFn
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFnA
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFnA
materialize_code Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFnA

theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFn_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFn.noFrames = true := by lit_decide

theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFnA_noFrames :
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFnA.noFrames = true := by lit_decide

end VG
