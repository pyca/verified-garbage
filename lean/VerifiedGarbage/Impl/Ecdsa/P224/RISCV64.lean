module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Window
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.P224

/-! # P-224 on RISC-V: four-word field elements and scalars, and `vg_p224_mul`

The functions modulo `p` and `n` are those of any four-word modulus
(`Impl/Weierstrass/RISCV64/Gen4.lean`), and `vg_p224_mul` is P-256's by
four-bit windows and Jacobian doublings (`Impl/Ecdsa/RISCV64/Window.lean`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_p224_mul_mod_p`. -/
def p224MulP : Prog isa := Weierstrass.RISCV64.Gen4.mulFn Impl.Weierstrass.Mont.p224p.m
/-- `vg_p224_add_mod_p`. -/
def p224AddP : Prog isa := Weierstrass.RISCV64.Gen4.addFn Impl.Weierstrass.Mont.p224p.m
/-- `vg_p224_sub_mod_p`. -/
def p224SubP : Prog isa := Weierstrass.RISCV64.Gen4.subFn Impl.Weierstrass.Mont.p224p.m
/-- `vg_p224_mul_mod_n`. -/
def p224MulN : Prog isa := Weierstrass.RISCV64.Gen4.mulFn Impl.Weierstrass.Mont.p224n.m
/-- `vg_p224_add_mod_n`. -/
def p224AddN : Prog isa := Weierstrass.RISCV64.Gen4.addFn Impl.Weierstrass.Mont.p224n.m
/-- `vg_p224_sub_mod_n`. -/
def p224SubN : Prog isa := Weierstrass.RISCV64.Gen4.subFn Impl.Weierstrass.Mont.p224n.m

/-- The functions of P-224's `p`. -/
def p224Field : Weierstrass.RISCV64.Field := ⟨Impl.Weierstrass.Mont.p224p, p224MulP, p224AddP, p224SubP⟩

/-- The functions of P-224's `n`. -/
def p224Order : Weierstrass.RISCV64.Field := ⟨Impl.Weierstrass.Mont.p224n, p224MulN, p224AddN, p224SubN⟩

/-- P-224 as the code has it. -/
def p224 : Cfg := { n := 4, C := Spec.P224.curve, FP := p224Field }

/-- `vg_p224_mul`, by windows. -/
def mulP224 : Prog isa := Window.Cfg.mulFn p224

end VG.Impl.Ecdsa.RISCV64
