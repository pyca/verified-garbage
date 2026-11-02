module

public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
import VerifiedGarbage.Proof.Rsa.RISCV64.IbInverse

/-! # The proofs supplied at the RSA registration on RISC-V

The batched inverse's and GCD's contract (`InvLaw`), proved in `IbInverse.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64

instance invLaw : InvLaw where
  inverse_ok := InvBatch.inverse_ok
  gcd_ok := InvBatch.gcd_ok

end VG.Proof.Rsa.RISCV64
