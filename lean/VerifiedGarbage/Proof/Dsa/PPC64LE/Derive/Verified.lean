module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Implies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_derive_key` on PPC64LE: verified against the shared contract

`dContract` states the shared contract on the registers and the stack
(`deriveKey_implies`, `Derive/Implies.lean`); with correctness
(`deriveKey_correct`) and constant time (`deriveKey_ct`), `Derive.derive` is
verified (`deriveKey_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_derive_key`. -/
theorem deriveKey_verified : Verified target Derive.derive (Spec.Dsa.deriveKeyContract abi) :=
  Verified.of_correct deriveKey_correct deriveKey_ct deriveKey_implies

end VG.Proof.Dsa.PPC64LE
