module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.RISCV64

/-! # ECDSA over brainpoolp512r1 on RISC-V: `vg_ecdsa_brainpoolp512r1_sign` and `vg_ecdsa_brainpoolp512r1_verify`

Signing computes `[k]G` by the ladder, `vg_brainpoolp512r1_mul`; verification's
joint ladder adds by the complete addition for any `a` (`brainpoolp512r1.am3 =
false`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp512r1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signBrainpoolP512r1 : Prog isa := Sign.Cfg.sign brainpoolp512r1 brainpoolp512r1Order "vg_brainpoolp512r1_mul" mulBrainpoolP512r1

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa :=
  Verify.Cfg.verify brainpoolp512r1 brainpoolp512r1Order "vg_brainpoolp512r1_check_point" Ecdh.RISCV64.checkBrainpoolP512r1

end VG.Impl.Ecdsa.RISCV64
