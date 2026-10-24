module

import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyImplies
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_verify` on PPC64LE: verified against the shared contract

`vContract` states the shared contract on the registers and the stack
(`verify_implies`, `VerifyImplies.lean`); with correctness (`verify_correct`) and constant time
(`verify_ct`), `Verify.verify` is verified (`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_verify`. -/
theorem verify_verified : Verified target Verify.verify (Spec.Dsa.verifyContract abi) :=
  Verified.of_correct verify_correct verify_ct verify_implies

end VG.Proof.Dsa.PPC64LE
