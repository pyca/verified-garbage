module

import VerifiedGarbage.Proof.Dsa.RISCV64.RSCT
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSImplies
public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign

/-!
# `vg_dsa_sign_random` on RISC-V: verified against the shared contract

`rsContract` states the shared contract on the registers and the stack
(`randomSign_implies`, `RSImplies.lean`); with correctness
(`randomSign_correct`, `RSFn.lean`) and constant time (`randomSign_ct`,
`RSCT.lean`), `RandomSign.code` is verified with its 192 bytes of stack
(`randomSign_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_sign_random`. -/
theorem randomSign_verified :
    Verified RISCV64.target RandomSign.code (Spec.Dsa.randomSignContract RISCV64.abi RS.rsStack) :=
  Verified.of_correct RS.randomSign_correct RS.randomSign_ct randomSign_implies

end VG.Proof.Dsa.RISCV64
