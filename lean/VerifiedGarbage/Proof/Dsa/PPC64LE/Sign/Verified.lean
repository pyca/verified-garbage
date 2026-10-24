module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Implies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_dsa_sign` on PPC64LE: verified against the shared contract

`sContract` states the shared contract on the registers and the stack
(`sign_implies`, `Sign/Implies.lean`); with correctness (`sign_correct`) and constant time
(`sign_ct`), `Sign.sign` is verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_sign`. -/
theorem sign_verified : Verified target Sign.sign (Spec.Dsa.signContract abi) :=
  Verified.of_correct sign_correct sign_ct sign_implies

end VG.Proof.Dsa.PPC64LE
