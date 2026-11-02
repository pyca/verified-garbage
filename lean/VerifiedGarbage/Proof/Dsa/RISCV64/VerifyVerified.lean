module

import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyCT
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_verify` on RISC-V: verified against the shared contract

`vContract` states the shared contract on the registers and the stack
(`verify_implies`, `VerifyImplies.lean`); with correctness (`verify_correct`,
`VerifyFn.lean`) and constant time (`verify_ct`, `VerifyCT.lean`),
`Verify.verify` is verified (`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_verify`. -/
theorem verify_verified : Verified RISCV64.target Verify.verify (Spec.Dsa.verifyContract RISCV64.abi) :=
  Verified.of_correct verify_correct CT.verify_ct verify_implies

end VG.Proof.Dsa.RISCV64
