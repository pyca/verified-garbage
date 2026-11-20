module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.RISCV64

/-! # ECDSA over brainpoolp320r1 on RISC-V: `vg_ecdsa_brainpoolp320r1_sign` and `vg_ecdsa_brainpoolp320r1_verify`

Signing computes `[k]G` by four-bit windows, `vg_brainpoolp320r1_mul`; verification's
joint ladder adds by the complete addition for any `a` (`brainpoolp320r1.am3 =
false`), and its `R = 4 R` is two Jacobian doublings by `dblJa`, for any `a`
(`Impl/Ecdsa/RISCV64/VerifyJ.lean`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp320r1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signBrainpoolP320r1 : Prog isa := Sign.Cfg.sign brainpoolp320r1 brainpoolp320r1Order "vg_brainpoolp320r1_mul" mulBrainpoolP320r1

/-- `vg_ecdsa_brainpoolp320r1_verify`. -/
def verifyBrainpoolP320r1 : Prog isa :=
  VerifyJ.Cfg.verify brainpoolp320r1 Impl.Weierstrass.dblJa brainpoolp320r1Order "vg_brainpoolp320r1_check_point" Ecdh.RISCV64.checkBrainpoolP320r1

end VG.Impl.Ecdsa.RISCV64
