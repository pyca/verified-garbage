module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb
public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Impl.P224.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.TCombWords

/-! # `vg_p224_mul_g` on RISC-V

P-224's comb for `[k]G`, `Impl/Ecdsa/RISCV64/Comb.lean`'s over P-224's
table (`Impl/P224/CombTable7.lean`): its words, slots and table's shape are
P-256's. A module of its own, as P-224's curve (`Impl/Ecdsa/P224/RISCV64.lean`)
imports the windows, which import the comb.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Comb

open VG.RISCV64 VG.Impl.Weierstrass

/-- The table's symbol. -/
def p224Sym : String := "VG_P224_COMB"

/-- The words of P-224's tables, in Montgomery's form. -/
@[irreducible] def p224CombWords : List (BitVec 64) :=
  tcombWords 4 (2 ^ 256) Spec.P224.curve.p Impl.P224.p224Comb7

def p224CombConsts : List (String × List (BitVec 64)) := [(p224Sym, p224CombWords)]

/-- `vg_p224_mul_g`. -/
def mulGP224 : Prog isa := Cfg.combFn p224 p224Sym Impl.P224.p224Comb7Start

/-- The name of `vg_p224_mul_g`. -/
def mulGP224Name : String := "vg_p224_mul_g"

end VG.Impl.Ecdsa.RISCV64.Comb
