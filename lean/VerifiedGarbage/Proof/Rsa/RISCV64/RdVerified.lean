module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdCorrect
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdCT

/-!
# `vg_rsa_recover_primes_det` on RISC-V: verified

`rd_verified`: correct (`rd_correct`, `RdCorrect.lean`), constant time
(`code_ct`, `RdCT.lean`), and the contract on the registers and the stack
implied by the shared contract (`rd_implies`, `RdFront.lean`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.RecDet

open VG VG.RISCV64

/-- `vg_rsa_recover_primes_det`. -/
theorem rd_verified :
    Verified RISCV64.target VG.Impl.Rsa.RISCV64.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract RISCV64.abi) :=
  Verified.of_correct rd_correct code_ct rd_implies

end VG.Proof.Rsa.RISCV64.RecDet
