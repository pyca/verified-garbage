module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64

/-! # ECDSA over brainpoolp384r1 on RISC-V: `vg_ecdsa_brainpoolp384r1_sign` and `vg_ecdsa_brainpoolp384r1_verify`

Signing computes `[k]G` by the ladder, `vg_brainpoolp384r1_mul`; verification's
joint ladder adds by the complete addition for any `a` (`brainpoolp384r1.am3 =
false`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp384r1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signBrainpoolP384r1 : Prog isa := Sign.Cfg.sign brainpoolp384r1 brainpoolp384r1Order "vg_brainpoolp384r1_mul" mulBrainpoolP384r1

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa :=
  Verify.Cfg.verify brainpoolp384r1 brainpoolp384r1Order "vg_brainpoolp384r1_check_point" Ecdh.RISCV64.checkBrainpoolP384r1

end VG.Impl.Ecdsa.RISCV64
