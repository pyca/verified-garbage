module

import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.SignImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_sign` on RISC-V: verified against the shared contract

`sContract` states the shared contract on the registers and the stack
(`sign_implies`, `SignImplies.lean`); with correctness (`sign_correct`,
`SignFn.lean`) and constant time (`sign_ct`, `SignCTB.lean`), `Sign.sign` is
verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_sign`. -/
theorem sign_verified : Verified RISCV64.target Sign.sign (Spec.Dsa.signContract RISCV64.abi) :=
  Verified.of_correct sign_correct CT.sign_ct sign_implies

end VG.Proof.Dsa.RISCV64
