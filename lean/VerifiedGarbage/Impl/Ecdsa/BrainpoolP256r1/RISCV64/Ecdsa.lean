module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.RISCV64

/-! # ECDSA over brainpoolp256r1 on RISC-V: `vg_ecdsa_brainpoolp256r1_sign` and `vg_ecdsa_brainpoolp256r1_verify`

Signing computes `[k]G` by the comb, `vg_brainpoolp256r1_mul_g`; verification
computes `[u]G + [v]Q` as `Impl/Ecdsa/RISCV64/VerifyComb.lean` does: `[v]Q` by
the windows of `vg_brainpoolp256r1_mul`, `[u]G` by the comb, and their sum by
the complete addition for any `a` (`brainpoolp256r1.am3 = false`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp256r1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signBrainpoolP256r1 : Prog isa :=
  Sign.Cfg.sign brainpoolp256r1 brainpoolp256r1Order Comb.mulGBrainpoolP256r1Name Comb.mulGBrainpoolP256r1

/-- `vg_ecdsa_brainpoolp256r1_verify`. -/
def verifyBrainpoolP256r1 : Prog isa :=
  VerifyComb.Cfg.verify brainpoolp256r1 brainpoolp256r1Order "vg_brainpoolp256r1_check_point" Ecdh.RISCV64.checkBrainpoolP256r1
    "vg_brainpoolp256r1_mul" mulBrainpoolP256r1 Comb.mulGBrainpoolP256r1Name Comb.mulGBrainpoolP256r1

end VG.Impl.Ecdsa.RISCV64
