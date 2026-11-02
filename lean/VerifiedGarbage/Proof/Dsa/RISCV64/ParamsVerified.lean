module

import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_dsa_check_parameters` on RISC-V: verified against its contract

`pcContract` states the contract on the registers
(`checkParameters_implies`); with correctness (`checkParameters_correct`) and
constant time (`check_ct`), `Params.checkParameters` is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_check_parameters`. -/
theorem checkParameters_verified :
    Verified RISCV64.target Params.checkParameters (Proof.Dsa.checkParametersContract RISCV64.abi) :=
  Verified.of_correct checkParameters_correct CT.check_ct checkParameters_implies

end VG.Proof.Dsa.RISCV64
