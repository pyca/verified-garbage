module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.BrainpoolP256r1

/-! # Arithmetic modulo brainpoolP256r1's prime on RISC-V: Montgomery's, for any four-word modulus (`Gen4`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.BrainpoolP256r1Field

open VG.RISCV64

/-- `vg_brainpoolp256r1_mul_mod_p`. -/
def mulFn : Prog isa := Gen4.mulFn Spec.BrainpoolP256r1.p

/-- `vg_brainpoolp256r1_add_mod_p`. -/
def addFn : Prog isa := Gen4.addFn Spec.BrainpoolP256r1.p

/-- `vg_brainpoolp256r1_sub_mod_p`. -/
def subFn : Prog isa := Gen4.subFn Spec.BrainpoolP256r1.p

/-- `vg_brainpoolp256r1_mul_mod_p`, for aligned offsets. -/
def mulFnA : Prog isa := Gen4.mulFnA Spec.BrainpoolP256r1.p

/-- `vg_brainpoolp256r1_add_mod_p`, for aligned offsets. -/
def addFnA : Prog isa := Gen4.addFnA Spec.BrainpoolP256r1.p

/-- `vg_brainpoolp256r1_sub_mod_p`, for aligned offsets. -/
def subFnA : Prog isa := Gen4.subFnA Spec.BrainpoolP256r1.p

end VG.Impl.Weierstrass.RISCV64.BrainpoolP256r1Field
