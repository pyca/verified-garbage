module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP256r1Field
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-! # brainpoolp256r1 on RISC-V: four-word field elements and scalars, and `vg_brainpoolp256r1_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of brainpoolP256r1's `p`. -/
def brainpoolp256r1Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp256r1p, Weierstrass.RISCV64.BrainpoolP256r1Field.mulFn,
    Weierstrass.RISCV64.BrainpoolP256r1Field.addFn, Weierstrass.RISCV64.BrainpoolP256r1Field.subFn⟩

/-- The functions of brainpoolP256r1's `n`. -/
def brainpoolp256r1Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.brainpoolp256r1n, Weierstrass.RISCV64.Gen4.mulFn Spec.BrainpoolP256r1.n,
    Weierstrass.RISCV64.Gen4.addFn Spec.BrainpoolP256r1.n, Weierstrass.RISCV64.Gen4.subFn Spec.BrainpoolP256r1.n⟩

/-- brainpoolp256r1 as the code has it. -/
def brainpoolp256r1 : Cfg := { n := 4, C := Spec.BrainpoolP256r1.curve, FP := brainpoolp256r1Field }

/-- `vg_brainpoolp256r1_mul`. -/
def mulBrainpoolP256r1 : Prog isa := brainpoolp256r1.mulFn

end VG.Impl.Ecdsa.RISCV64
