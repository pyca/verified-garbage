module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Implies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_check_parameters` on PPC64LE: verified against the shared contract

`pcContract` states the shared contract on the registers
(`checkParameters_implies`, `Params/Implies.lean`); with correctness
(`checkParameters_correct`) and constant time (`checkParameters_ct`),
`Params.checkParameters` is verified (`checkParameters_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_check_parameters`. -/
theorem checkParameters_verified :
    Verified target Params.checkParameters (Proof.Dsa.checkParametersContract abi) :=
  Verified.of_correct checkParameters_correct checkParameters_ct checkParameters_implies

end VG.Proof.Dsa.PPC64LE
