module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-384's prime on RISC-V: the code as literals

The three functions as literals (`materialize_code`,
`Proof/Framework/Lit.lean`), which the literals of their callers refer to,
and which the absence of frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.P384Field.mulFn
materialize_code Impl.Weierstrass.RISCV64.P384Field.addFn
materialize_code Impl.Weierstrass.RISCV64.P384Field.subFn

theorem Impl.Weierstrass.RISCV64.P384Field.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.P384Field.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P384Field.addFn_noFrames :
    Impl.Weierstrass.RISCV64.P384Field.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P384Field.subFn_noFrames :
    Impl.Weierstrass.RISCV64.P384Field.subFn.noFrames = true := by lit_decide

end VG
