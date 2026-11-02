module

import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCTB
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_derive_key` on RISC-V: verified against the shared contract

`dContract` states the shared contract on the registers and the stack
(`deriveKey_implies`, `DeriveImplies.lean`); with correctness
(`deriveKey_correct`, `DeriveFn.lean`) and constant time (`derive_ct`,
`DeriveCTB.lean`), `Derive.derive` is verified (`deriveKey_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_derive_key`. -/
theorem deriveKey_verified :
    Verified RISCV64.target Derive.derive (Spec.Dsa.deriveKeyContract RISCV64.abi) :=
  Verified.of_correct deriveKey_correct CT.derive_ct deriveKey_implies

end VG.Proof.Dsa.RISCV64
