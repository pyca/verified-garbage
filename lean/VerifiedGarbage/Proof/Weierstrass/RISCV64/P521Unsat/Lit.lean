module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Unsat
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Unsat
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Arithmetic modulo P-521's prime in 58-bit limbs, on RISC-V: the code as literals

The functions as literals (`materialize_code`, `Proof/Framework/Lit.lean`),
which the literals of their callers refer to, and which the absence of
frames their calls need evaluates.
-/

@[expose] public section

namespace VG

materialize_code Impl.Weierstrass.RISCV64.P521Unsat.mulFn
materialize_code Impl.Weierstrass.RISCV64.P521Unsat.mulFnA
materialize_code Impl.Weierstrass.RISCV64.P521Unsat.addFn
materialize_code Impl.Weierstrass.RISCV64.P521Unsat.subFn
materialize_code Impl.Weierstrass.RISCV64.P521Unsat.unpackFn
materialize_code Impl.Weierstrass.RISCV64.P521Unsat.packFn

theorem Impl.Weierstrass.RISCV64.P521Unsat.mulFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.mulFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Unsat.mulFnA_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.mulFnA.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Unsat.addFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.addFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Unsat.subFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.subFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Unsat.unpackFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.unpackFn.noFrames = true := by lit_decide
theorem Impl.Weierstrass.RISCV64.P521Unsat.packFn_noFrames :
    Impl.Weierstrass.RISCV64.P521Unsat.packFn.noFrames = true := by lit_decide

end VG
