module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-! # Arithmetic modulo brainpoolP512r1's prime on RISC-V: Montgomery's, for any modulus of seven words or more (`GenWide`), at eight words, squaring when the operands are the same -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field

open VG.RISCV64

/-- `vg_brainpoolp512r1_mul_mod_p`. -/
def mulFn : Prog isa := GenWide.mulSqFn 8 Impl.Weierstrass.Mont.brainpoolp512r1p.m

/-- `vg_brainpoolp512r1_add_mod_p`. -/
def addFn : Prog isa := GenWide.addFn 8 Impl.Weierstrass.Mont.brainpoolp512r1p.m

/-- `vg_brainpoolp512r1_sub_mod_p`. -/
def subFn : Prog isa := GenWide.subFn 8 Impl.Weierstrass.Mont.brainpoolp512r1p.m

end VG.Impl.Weierstrass.RISCV64.BrainpoolP512r1Field
