module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen5
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-! # Arithmetic modulo brainpoolP320r1's order on RISC-V: Montgomery's, for any five-word modulus (`Gen5`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP320r1Order

open VG.RISCV64

/-- `vg_brainpoolp320r1_mul_mod_n`. -/
def mulFn : Prog isa := Gen5.mulFn Impl.Weierstrass.Mont.brainpoolp320r1n.m

/-- `vg_brainpoolp320r1_add_mod_n`. -/
def addFn : Prog isa := Gen5.addFn Impl.Weierstrass.Mont.brainpoolp320r1n.m

/-- `vg_brainpoolp320r1_sub_mod_n`. -/
def subFn : Prog isa := Gen5.subFn Impl.Weierstrass.Mont.brainpoolp320r1n.m

/-- `vg_brainpoolp320r1_mul_mod_n`, for aligned offsets. -/
def mulFnA : Prog isa := Gen5.mulFnA Impl.Weierstrass.Mont.brainpoolp320r1n.m

/-- `vg_brainpoolp320r1_add_mod_n`, for aligned offsets. -/
def addFnA : Prog isa := Gen5.addFnA Impl.Weierstrass.Mont.brainpoolp320r1n.m

/-- `vg_brainpoolp320r1_sub_mod_n`, for aligned offsets. -/
def subFnA : Prog isa := Gen5.subFnA Impl.Weierstrass.Mont.brainpoolp320r1n.m

end VG.Impl.Weierstrass.RISCV64.BrainpoolP320r1Order
