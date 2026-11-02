module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-! # Arithmetic modulo brainpoolP512r1's order on RISC-V: Montgomery's, for any modulus of seven words or more (`GenWide`), at eight words -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP512r1Order

open VG.RISCV64

/-- `vg_brainpoolp512r1_mul_mod_n`. -/
def mulFn : Prog isa := GenWide.mulFn 8 Impl.Weierstrass.Mont.brainpoolp512r1n.m

/-- `vg_brainpoolp512r1_add_mod_n`. -/
def addFn : Prog isa := GenWide.addFn 8 Impl.Weierstrass.Mont.brainpoolp512r1n.m

/-- `vg_brainpoolp512r1_sub_mod_n`. -/
def subFn : Prog isa := GenWide.subFn 8 Impl.Weierstrass.Mont.brainpoolp512r1n.m

end VG.Impl.Weierstrass.RISCV64.BrainpoolP512r1Order
