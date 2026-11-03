module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP256r1Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP256r1Order
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-! # brainpoolp256r1 on RISC-V: four-word field elements and scalars, and `vg_brainpoolp256r1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of brainpoolP256r1's `p`. -/
def brainpoolp256r1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp256r1p, Weierstrass.RISCV64.BrainpoolP256r1Field.mulFn,
    Weierstrass.RISCV64.BrainpoolP256r1Field.addFn, Weierstrass.RISCV64.BrainpoolP256r1Field.subFn,
    Weierstrass.RISCV64.BrainpoolP256r1Field.mulFnA, Weierstrass.RISCV64.BrainpoolP256r1Field.addFnA,
    Weierstrass.RISCV64.BrainpoolP256r1Field.subFnA⟩

/-- The functions of brainpoolP256r1's `n`. -/
def brainpoolp256r1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp256r1n, Weierstrass.RISCV64.BrainpoolP256r1Order.mulFn,
    Weierstrass.RISCV64.BrainpoolP256r1Order.addFn, Weierstrass.RISCV64.BrainpoolP256r1Order.subFn,
    Weierstrass.RISCV64.BrainpoolP256r1Order.mulFnA, Weierstrass.RISCV64.BrainpoolP256r1Order.addFnA,
    Weierstrass.RISCV64.BrainpoolP256r1Order.subFnA⟩

/-- brainpoolP256r1 as the code has it: `a ≠ -3`, so verification adds by the
complete addition for any `a` (`am3 := false`). -/
def brainpoolp256r1 : Cfg := { n := 4, C := Spec.BrainpoolP256r1.curve, FP := brainpoolp256r1Field, am3 := false }

/-- `vg_brainpoolp256r1_mul`, by four-bit windows with the Jacobian doubling for
any `a` (`Impl/Ecdsa/RISCV64/WindowA.lean`). -/
def mulBrainpoolP256r1 : Prog isa := WindowA.Cfg.mulFn brainpoolp256r1 WindowA.dblJa

end VG.Impl.Ecdsa.RISCV64
