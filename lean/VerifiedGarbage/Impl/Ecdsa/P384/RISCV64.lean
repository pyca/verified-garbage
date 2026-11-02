module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Order
public import VerifiedGarbage.Spec.P384

/-! # P-384 on RISC-V: six-word field elements and scalars, and `vg_p384_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of P-384's `p`. -/
def p384Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.p384p, Weierstrass.RISCV64.P384Field.mulFn, Weierstrass.RISCV64.P384Field.addFn,
    Weierstrass.RISCV64.P384Field.subFn⟩

/-- The functions of P-384's `n`. -/
def p384Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.p384n, Weierstrass.RISCV64.P384Order.mulFn, Weierstrass.RISCV64.P384Order.addFn,
    Weierstrass.RISCV64.P384Order.subFn⟩

/-- P-384 as the code has it. -/
def p384 : Cfg := { n := 6, C := Spec.P384.curve, FP := p384Field }

/-- `vg_p384_mul`. -/
def mulP384 : Prog isa := p384.mulFn

end VG.Impl.Ecdsa.RISCV64
