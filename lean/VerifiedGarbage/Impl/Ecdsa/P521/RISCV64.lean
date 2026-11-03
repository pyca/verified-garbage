module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowU

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Field
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Order
public import VerifiedGarbage.Spec.P521

/-! # P-521 on RISC-V: nine-word field elements and scalars, and `vg_p521_mul` -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- The functions of P-521's `p`. -/
def p521Field : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.p521p, Weierstrass.RISCV64.P521Field.mulFn,
    Weierstrass.RISCV64.P521Field.addFn, Weierstrass.RISCV64.P521Field.subFn,
    Weierstrass.RISCV64.P521Field.mulFnA, Weierstrass.RISCV64.P521Field.addFnA,
    Weierstrass.RISCV64.P521Field.subFnA⟩

/-- The functions of P-521's `n`. -/
def p521Order : Weierstrass.RISCV64.Field :=
  ⟨Impl.Weierstrass.Mont.p521n, Weierstrass.RISCV64.P521Order.mulFn,
    Weierstrass.RISCV64.P521Order.addFn, Weierstrass.RISCV64.P521Order.subFn,
    Weierstrass.RISCV64.P521Order.mulFnA, Weierstrass.RISCV64.P521Order.addFnA,
    Weierstrass.RISCV64.P521Order.subFnA⟩

/-- P-521 as the code has it. -/
def p521 : Cfg := { n := 9, C := Spec.P521.curve, FP := p521Field }

/-- `vg_p521_mul`, by four-bit windows in 58-bit limbs
(`Impl/Ecdsa/RISCV64/WindowU.lean`). -/
def mulP521 : Prog isa := WindowU.mulFn

end VG.Impl.Ecdsa.RISCV64
