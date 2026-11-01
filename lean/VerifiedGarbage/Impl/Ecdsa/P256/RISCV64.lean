module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P256Order
public import VerifiedGarbage.Spec.P256

/-! # P-256 on RISC-V: four-word field elements and scalars, and `vg_p256_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of P-256's `p`. -/
def p256Field : Weierstrass.RISCV64.Field :=
  ⟨Spec.Weierstrass.Mont.p256p, Weierstrass.RISCV64.P256Field.mulFn, Weierstrass.RISCV64.P256Field.addFn,
    Weierstrass.RISCV64.P256Field.subFn⟩

/-- The functions of P-256's `n`. -/
def p256Order : Weierstrass.RISCV64.Field :=
  ⟨Spec.Weierstrass.Mont.p256n, Weierstrass.RISCV64.P256Order.mulFn, Weierstrass.RISCV64.P256Order.addFn,
    Weierstrass.RISCV64.P256Order.subFn⟩

/-- P-256 as the code has it. -/
def p256 : Cfg := { n := 4, C := Spec.P256.curve, FP := p256Field }

/-- `vg_p256_mul`. -/
def mulP256 : Prog isa := p256.mulFn

end VG.Impl.Ecdsa.RISCV64
