module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64

/-! # ECDSA over secp256k1 on RISC-V: `vg_ecdsa_secp256k1_sign` and `vg_ecdsa_secp256k1_verify`

Signing computes `[k]G` by the ladder, `vg_secp256k1_mul`; verification's
joint ladder adds by the complete addition for any `a` (`secp256k1.am3 =
false`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_secp256k1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signSecp256k1 : Prog isa := Sign.Cfg.sign secp256k1 secp256k1Order "vg_secp256k1_mul" mulSecp256k1

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa :=
  Verify.Cfg.verify secp256k1 secp256k1Order "vg_secp256k1_check_point" Ecdh.RISCV64.checkSecp256k1

end VG.Impl.Ecdsa.RISCV64
