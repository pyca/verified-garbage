module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384

/-!
# ECDSA verification over P-256 and P-384 on RISC-V, as emitted

`vg_ecdsa_p256_verify` and `vg_ecdsa_p384_verify`: `VerifyHash.verifyHash` of
the curve's verification (`VerifyComb.lean`), then its cleanup
(`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers cleared but the 32
bits of its result, and the 80 bytes of stack its frames use zeroed, so that
it returns without secret residue.
-/

-- separate module: `VerifyComb.lean` has 20 importers, which these definitions, read only by their theorems, would rebuild

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Fn

open VG.RISCV64

/-- `vg_ecdsa_p256_verify` as emitted. -/
def verifyP256 : Prog isa :=
  Impl.Scrub.RISCV64.scrubAll 32 80
    (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
      Impl.Ecdsa.RISCV64.VerifyComb.verifyP256)

/-- `vg_ecdsa_p384_verify` as emitted. -/
def verifyP384 : Prog isa :=
  Impl.Scrub.RISCV64.scrubAll 32 80
    (Impl.Ecdsa.RISCV64.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.RISCV64.VerifyComb.verifyP384)

end VG.Impl.Ecdsa.RISCV64.Fn
