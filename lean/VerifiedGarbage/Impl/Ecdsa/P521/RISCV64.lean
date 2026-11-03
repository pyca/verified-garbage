module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA

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

/-- P-521 as `vg_p521_mul`'s four-bit windows have it: the table at 4096, past
the slots, the entry `E` in slots 46 to 48, which the contract lets it write,
and the complete addition for any `a`, from `a` and `3 b`, which the
contract's caller provides (`am3 := false`); the doublings are those for
`a = -3`. -/
def p521w : Cfg := { p521 with jt := 4096, ve := 46, am3 := false }

/-- `vg_p521_mul`, by four-bit windows with the Jacobian doubling for `a = -3`
(`Impl/Ecdsa/RISCV64/WindowA.lean`). -/
def mulP521 : Prog isa := WindowA.Cfg.mulFn p521w Impl.Weierstrass.dblJ

end VG.Impl.Ecdsa.RISCV64
