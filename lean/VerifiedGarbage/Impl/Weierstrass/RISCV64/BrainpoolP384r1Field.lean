module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen6
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-! # Arithmetic modulo brainpoolP384r1's prime on RISC-V: Montgomery's, for any six-word modulus (`Gen6`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP384r1Field

open VG.RISCV64

/-- `vg_brainpoolp384r1_mul_mod_p`. -/
def mulFn : Prog isa := Gen6.mulFn Impl.Weierstrass.Mont.brainpoolp384r1p.m

/-- `vg_brainpoolp384r1_add_mod_p`. -/
def addFn : Prog isa := Gen6.addFn Impl.Weierstrass.Mont.brainpoolp384r1p.m

/-- `vg_brainpoolp384r1_sub_mod_p`. -/
def subFn : Prog isa := Gen6.subFn Impl.Weierstrass.Mont.brainpoolp384r1p.m

end VG.Impl.Weierstrass.RISCV64.BrainpoolP384r1Field
