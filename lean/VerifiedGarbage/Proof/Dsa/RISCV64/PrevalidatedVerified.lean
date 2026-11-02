module

import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedCT
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedFn
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_verify_prevalidated` on RISC-V: verified against the shared contract

`vpContract` states the shared contract on the registers and the stack
(`prevalidated_implies`); with correctness (`prevalidated_correct`) and
constant time (`prevalidated_ct`), `Prevalidated.verify` is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_verify_prevalidated`. -/
theorem prevalidated_verified :
    Verified RISCV64.target Prevalidated.verify (Spec.Dsa.verifyPrevalidatedContract RISCV64.abi) :=
  Verified.of_correct prevalidated_correct CT.prevalidated_ct prevalidated_implies

end VG.Proof.Dsa.RISCV64
