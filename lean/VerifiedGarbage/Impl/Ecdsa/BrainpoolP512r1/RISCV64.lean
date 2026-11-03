module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Order
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-! # brainpoolP512r1 on RISC-V: eight-word field elements and scalars, and `vg_brainpoolp512r1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of brainpoolP512r1's `p`. -/
def brainpoolp512r1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp512r1p, Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn,
    Weierstrass.RISCV64.BrainpoolP512r1Field.addFn, Weierstrass.RISCV64.BrainpoolP512r1Field.subFn,
    Weierstrass.RISCV64.BrainpoolP512r1Field.mulFnA, Weierstrass.RISCV64.BrainpoolP512r1Field.addFnA,
    Weierstrass.RISCV64.BrainpoolP512r1Field.subFnA⟩

/-- The functions of brainpoolP512r1's `n`. -/
def brainpoolp512r1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp512r1n, Weierstrass.RISCV64.BrainpoolP512r1Order.mulFn,
    Weierstrass.RISCV64.BrainpoolP512r1Order.addFn, Weierstrass.RISCV64.BrainpoolP512r1Order.subFn,
    Weierstrass.RISCV64.BrainpoolP512r1Order.mulFnA, Weierstrass.RISCV64.BrainpoolP512r1Order.addFnA,
    Weierstrass.RISCV64.BrainpoolP512r1Order.subFnA⟩

/-- brainpoolP512r1 as the code has it: `a ≠ -3`, so verification adds by the
complete addition for any `a` (`am3 := false`). -/
def brainpoolp512r1 : Cfg :=
  { n := 8, C := Spec.BrainpoolP512r1.curve, FP := brainpoolp512r1Field, jt := 4096, am3 := false }

/-- `vg_brainpoolp512r1_mul`, by four-bit windows with the Jacobian doubling for
any `a` (`Impl/Ecdsa/RISCV64/WindowA.lean`). -/
def mulBrainpoolP512r1 : Prog isa := WindowA.Cfg.mulFn brainpoolp512r1 WindowA.dblJa

end VG.Impl.Ecdsa.RISCV64
