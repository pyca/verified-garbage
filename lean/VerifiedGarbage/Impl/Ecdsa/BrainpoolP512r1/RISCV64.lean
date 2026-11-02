module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP512r1Order
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-! # brainpoolP512r1 on RISC-V: eight-word field elements and scalars, and `vg_brainpoolp512r1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of brainpoolP512r1's `p`. -/
def brainpoolp512r1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp512r1p, Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn, Weierstrass.RISCV64.BrainpoolP512r1Field.addFn,
    Weierstrass.RISCV64.BrainpoolP512r1Field.subFn⟩

/-- The functions of brainpoolP512r1's `n`. -/
def brainpoolp512r1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp512r1n, Weierstrass.RISCV64.BrainpoolP512r1Order.mulFn,
    Weierstrass.RISCV64.BrainpoolP512r1Order.addFn, Weierstrass.RISCV64.BrainpoolP512r1Order.subFn⟩

/-- brainpoolP512r1 as the code has it: `a ≠ -3`, so verification adds by the
complete addition for any `a` (`am3 := false`). -/
def brainpoolp512r1 : Cfg :=
  { n := 8, C := Spec.BrainpoolP512r1.curve, FP := brainpoolp512r1Field, jt := 4096, am3 := false }

/-- `vg_brainpoolp512r1_mul`. -/
def mulBrainpoolP512r1 : Prog isa := brainpoolp512r1.mulFn

end VG.Impl.Ecdsa.RISCV64
