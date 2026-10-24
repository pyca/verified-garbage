module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Implies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_validate_public_key` on PPC64LE: verified against the shared contract

`vkContract` states the shared contract on the registers
(`validate_implies`, `Validate/Implies.lean`); with correctness
(`validate_correct`) and constant time (`validate_ct`),
`Prevalidated.validate` is verified (`validate_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_validate_public_key`. -/
theorem validate_verified :
    Verified target Prevalidated.validate (Spec.Dsa.validatePublicKeyContract abi) :=
  Verified.of_correct validate_correct validate_ct validate_implies

end VG.Proof.Dsa.PPC64LE
