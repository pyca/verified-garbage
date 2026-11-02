module

import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCT
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_rsa_private_crt` on RISC-V: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`crt_implies`); with correctness (`fn_correct`) and constant time
(`fn_ct`), `crt` is verified (`crt_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64.Crt

/-- `vg_rsa_private_crt`. -/
theorem crt_verified : Verified RISCV64.target crt (Proof.Rsa.privateCrtContract RISCV64.abi) :=
  Verified.of_correct fn_correct fn_ct crt_implies

end VG.Proof.Bignum.RISCV64.Crt
