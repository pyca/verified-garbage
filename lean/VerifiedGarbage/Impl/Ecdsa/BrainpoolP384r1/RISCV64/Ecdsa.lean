module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1

/-! # ECDSA over brainpoolp384r1 on RISC-V: `vg_ecdsa_brainpoolp384r1_sign` and `vg_ecdsa_brainpoolp384r1_verify`

Signing computes `[k]G` by four-bit windows, `vg_brainpoolp384r1_mul`; verification's
joint ladder adds by the complete addition for any `a` (`brainpoolp384r1.am3 =
false`), and its `R = 4 R` is two Jacobian doublings by `dblJa`, for any `a`
(`Impl/Ecdsa/RISCV64/VerifyJ.lean`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp384r1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signBrainpoolP384r1 : Prog isa := Sign.Cfg.sign brainpoolp384r1 brainpoolp384r1Order "vg_brainpoolp384r1_mul" mulBrainpoolP384r1

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa :=
  VerifyJ.Cfg.verify brainpoolp384r1 Impl.Weierstrass.dblJa brainpoolp384r1Order "vg_brainpoolp384r1_check_point" Ecdh.RISCV64.checkBrainpoolP384r1

end VG.Impl.Ecdsa.RISCV64

/-! ## Verification as emitted

`vg_ecdsa_brainpoolp384r1_verify`: `VerifyHash.verifyHash` of the curve's verification,
then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers
cleared but the 32 bits of its result, and the 80 bytes of stack its frames
use zeroed, so that it returns without secret residue. -/

namespace VG.Impl.Ecdsa.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdsa_brainpoolp384r1_verify` as emitted. -/
def verifyBrainpoolP384r1 : Prog isa :=
  Impl.Scrub.RISCV64.scrubAll 32 80
    (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifyBrainpoolP384r1)

end VG.Impl.Ecdsa.RISCV64.Fn
