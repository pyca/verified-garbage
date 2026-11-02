module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Spec.Secp256k1

/-! # Arithmetic modulo secp256k1's order on RISC-V: Montgomery's, for any four-word modulus (`Gen4`) -/

@[expose] public section

namespace VG.Impl.Weierstrass.RISCV64.Secp256k1Order

open VG.RISCV64

/-- `vg_secp256k1_mul_mod_n`. -/
def mulFn : Prog isa := Gen4.mulFn Spec.Secp256k1.n

/-- `vg_secp256k1_add_mod_n`. -/
def addFn : Prog isa := Gen4.addFn Spec.Secp256k1.n

/-- `vg_secp256k1_sub_mod_n`. -/
def subFn : Prog isa := Gen4.subFn Spec.Secp256k1.n

end VG.Impl.Weierstrass.RISCV64.Secp256k1Order
