module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.RISCV64
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1

/-! # ECDSA over secp256k1 on RISC-V: `vg_ecdsa_secp256k1_sign` and `vg_ecdsa_secp256k1_verify`

Signing computes `[k]G` by the comb, `vg_secp256k1_mul_g`; verification
computes `[u]G + [v]Q` as `Impl/Ecdsa/RISCV64/VerifyComb.lean` does: `[v]Q` by
the windows of `vg_secp256k1_mul`, `[u]G` by the comb, and their sum by the
complete addition for any `a` (`secp256k1.am3 = false`). -/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64

/-- `vg_ecdsa_secp256k1_sign`, the signature for a nonce, which RFC 6979's
function calls. -/
def signSecp256k1 : Prog isa :=
  Sign.Cfg.sign secp256k1 secp256k1Order Comb.mulGSecp256k1Name Comb.mulGSecp256k1

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa :=
  VerifyComb.Cfg.verify secp256k1 secp256k1Order "vg_secp256k1_check_point" Ecdh.RISCV64.checkSecp256k1
    "vg_secp256k1_mul" mulSecp256k1 Comb.mulGSecp256k1Name Comb.mulGSecp256k1

end VG.Impl.Ecdsa.RISCV64

/-! ## Verification as emitted

`vg_ecdsa_secp256k1_verify`: `VerifyHash.verifyHash` of the curve's verification,
then its cleanup (`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers
cleared but the 32 bits of its result, and the 80 bytes of stack its frames
use zeroed, so that it returns without secret residue. -/

namespace VG.Impl.Ecdsa.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdsa_secp256k1_verify` as emitted. -/
def verifySecp256k1 : Prog isa :=
  Impl.Scrub.RISCV64.scrubAll 32 80
    (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
      Impl.Ecdsa.RISCV64.verifySecp256k1)

end VG.Impl.Ecdsa.RISCV64.Fn
