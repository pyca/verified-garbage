module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.P192

/-! # P-192 on RISC-V: four-word field elements and scalars, and `vg_p192_mul`

P-192's `p` and `n` are below `2¹⁹²`, and its numbers are kept in four words
whose top one is zero, so that the functions modulo `p` and `n` are those of
any four-word modulus (`Impl/Weierstrass/RISCV64/Gen4.lean`), and
`vg_p192_mul` is the ladder of P-224, P-256 and P-384, over the four words
of the scalar.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- P-192's `p`, as a four-word modulus. -/
def p192p4 : Weierstrass.Mont.Modulus := { Impl.Weierstrass.Mont.p192p with k := 4 }
/-- P-192's `n`, as a four-word modulus. -/
def p192n4 : Weierstrass.Mont.Modulus := { Impl.Weierstrass.Mont.p192n with k := 4 }

/-- `vg_p192_mul_mod_p`. -/
def p192MulP : Prog isa := Weierstrass.RISCV64.Gen4.mulFn p192p4.m
/-- `vg_p192_add_mod_p`. -/
def p192AddP : Prog isa := Weierstrass.RISCV64.Gen4.addFn p192p4.m
/-- `vg_p192_sub_mod_p`. -/
def p192SubP : Prog isa := Weierstrass.RISCV64.Gen4.subFn p192p4.m
/-- `vg_p192_mul_mod_n`. -/
def p192MulN : Prog isa := Weierstrass.RISCV64.Gen4.mulFn p192n4.m
/-- `vg_p192_add_mod_n`. -/
def p192AddN : Prog isa := Weierstrass.RISCV64.Gen4.addFn p192n4.m
/-- `vg_p192_sub_mod_n`. -/
def p192SubN : Prog isa := Weierstrass.RISCV64.Gen4.subFn p192n4.m

/-- The functions of P-192's `p`. -/
def p192Field : Weierstrass.RISCV64.Field := ⟨p192p4, p192MulP, p192AddP, p192SubP⟩

/-- The functions of P-192's `n`. -/
def p192Order : Weierstrass.RISCV64.Field := ⟨p192n4, p192MulN, p192AddN, p192SubN⟩

/-- P-192 as the code has it. -/
def p192 : Cfg := { n := 4, C := Spec.P192.curve, FP := p192Field }

/-- `vg_p192_mul`. -/
def mulP192 : Prog isa := p192.mulFn

end VG.Impl.Ecdsa.RISCV64
