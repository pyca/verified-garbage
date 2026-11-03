module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen6
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-! # Arithmetic modulo brainpoolP384r1's order on RISC-V: Montgomery's, for any six-word modulus (`Gen6`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP384r1Order

open VG.RISCV64

/-- `vg_brainpoolp384r1_mul_mod_n`. -/
def mulFn : Prog isa := Gen6.mulFn Impl.Weierstrass.Mont.brainpoolp384r1n.m

/-- `vg_brainpoolp384r1_add_mod_n`. -/
def addFn : Prog isa := Gen6.addFn Impl.Weierstrass.Mont.brainpoolp384r1n.m

/-- `vg_brainpoolp384r1_sub_mod_n`. -/
def subFn : Prog isa := Gen6.subFn Impl.Weierstrass.Mont.brainpoolp384r1n.m

/-- `vg_brainpoolp384r1_mul_mod_n`, for aligned offsets. -/
def mulFnA : Prog isa := Gen6.mulFnA Impl.Weierstrass.Mont.brainpoolp384r1n.m

/-- `vg_brainpoolp384r1_add_mod_n`, for aligned offsets. -/
def addFnA : Prog isa := Gen6.addFnA Impl.Weierstrass.Mont.brainpoolp384r1n.m

/-- `vg_brainpoolp384r1_sub_mod_n`, for aligned offsets. -/
def subFnA : Prog isa := Gen6.subFnA Impl.Weierstrass.Mont.brainpoolp384r1n.m

end VG.Impl.Weierstrass.RISCV64.BrainpoolP384r1Order
