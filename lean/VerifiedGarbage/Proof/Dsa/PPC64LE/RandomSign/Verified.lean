module

import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign

/-!
# `vg_dsa_sign_random` on PPC64LE: verified against the shared contract

`rsContract` states the shared contract on the registers and the stack
(`randomSign_implies`); with correctness (`randomSign_correct`) and constant
time (`randomSign_ct`), `RandomSign.code` is verified with its 304 bytes of
stack (`randomSign_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_sign_random`. -/
theorem randomSign_verified :
    Verified target Impl.Dsa.PPC64LE.RandomSign.code (Spec.Dsa.randomSignContract abi rsStack) :=
  Verified.of_correct RS.randomSign_correct RS.randomSign_ct randomSign_implies

end VG.Proof.Dsa.PPC64LE
