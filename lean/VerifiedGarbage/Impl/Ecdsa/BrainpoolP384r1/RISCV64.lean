module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP384r1Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen6
public import VerifiedGarbage.Spec.BrainpoolP384r1

/-! # brainpoolP384r1 on RISC-V: six-word field elements and scalars, and `vg_brainpoolp384r1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of brainpoolP384r1's `p`. -/
def brainpoolp384r1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp384r1p, Weierstrass.RISCV64.BrainpoolP384r1Field.mulFn, Weierstrass.RISCV64.BrainpoolP384r1Field.addFn,
    Weierstrass.RISCV64.BrainpoolP384r1Field.subFn⟩

/-- The functions of brainpoolP384r1's `n`. -/
def brainpoolp384r1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp384r1n, Weierstrass.RISCV64.Gen6.mulFn Impl.Weierstrass.Mont.brainpoolp384r1n.m,
    Weierstrass.RISCV64.Gen6.addFn Impl.Weierstrass.Mont.brainpoolp384r1n.m,
    Weierstrass.RISCV64.Gen6.subFn Impl.Weierstrass.Mont.brainpoolp384r1n.m⟩

/-- brainpoolP384r1 as the code has it. -/
def brainpoolp384r1 : Cfg := { n := 6, C := Spec.BrainpoolP384r1.curve, FP := brainpoolp384r1Field, jt := 4096 }

/-- `vg_brainpoolp384r1_mul`. -/
def mulBrainpoolP384r1 : Prog isa := brainpoolp384r1.mulFn

end VG.Impl.Ecdsa.RISCV64
