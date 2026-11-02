module

import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateCT
import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_validate_public_key` on RISC-V: verified against the shared contract

`vkContract` states the shared contract on the registers
(`validate_implies`); with correctness (`validate_correct`) and constant time
(`validate_ct`), `Prevalidated.validate` is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_validate_public_key`. -/
theorem validate_verified :
    Verified RISCV64.target Prevalidated.validate (Spec.Dsa.validatePublicKeyContract RISCV64.abi) :=
  Verified.of_correct validate_correct CT.validate_ct validate_implies

end VG.Proof.Dsa.RISCV64
