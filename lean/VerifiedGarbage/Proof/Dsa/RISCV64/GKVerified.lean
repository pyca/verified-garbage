module

import VerifiedGarbage.Proof.Dsa.RISCV64.GKCT
import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKImplies
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate

/-!
# `vg_dsa_generate_key` on RISC-V: verified against the shared contract

`gkContract` states the shared contract on the registers and the stack
(`generate_implies`, `GKImplies.lean`); with correctness
(`generate_correct`, `GKFn.lean`) and constant time (`generate_ct`,
`GKCT.lean`), `Generate.code` is verified with its 192 bytes of stack
(`generateKey_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_generate_key`. -/
theorem generateKey_verified :
    Verified RISCV64.target Generate.code (Spec.Dsa.generateKeyContract RISCV64.abi GK.gkStack) :=
  Verified.of_correct GK.generate_correct GK.generate_ct generate_implies

end VG.Proof.Dsa.RISCV64
