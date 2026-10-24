module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Implies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_verify_prevalidated` on PPC64LE: verified against the shared contract

`vpContract` states the shared contract on the registers and the stack
(`prevalidated_implies`, `Prevalidated/Implies.lean`); with correctness
(`prevalidated_correct`) and constant time (`prevalidated_ct`),
`Prevalidated.verify` is verified (`prevalidated_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_verify_prevalidated`. -/
theorem prevalidated_verified :
    Verified target Prevalidated.verify (Spec.Dsa.verifyPrevalidatedContract abi) :=
  Verified.of_correct prevalidated_correct prevalidated_ct prevalidated_implies

end VG.Proof.Dsa.PPC64LE
