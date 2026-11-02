module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.Secp256k1

/-! # Arithmetic modulo secp256k1's prime on RISC-V: Montgomery's, for any four-word modulus (`Gen4`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Secp256k1Field

open VG.RISCV64

/-- `vg_secp256k1_mul_mod_p`. -/
def mulFn : Prog isa := Gen4.mulFn Spec.Secp256k1.p

/-- `vg_secp256k1_add_mod_p`. -/
def addFn : Prog isa := Gen4.addFn Spec.Secp256k1.p

/-- `vg_secp256k1_sub_mod_p`. -/
def subFn : Prog isa := Gen4.subFn Spec.Secp256k1.p

end VG.Impl.Weierstrass.RISCV64.Secp256k1Field
