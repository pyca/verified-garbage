module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate

/-!
# `vg_dsa_generate_key` on PPC64LE: verified against the shared contract

`gkContract` states the shared contract on the registers and the stack
(`generate_implies`); with correctness (`generate_correct`) and constant
time (`generate_ct`), `Generate.code` is verified with its 304 bytes of
stack (`generate_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_generate_key`. -/
theorem generate_verified :
    Verified target Impl.Dsa.PPC64LE.Generate.code (Spec.Dsa.generateKeyContract abi gkStack) :=
  Verified.of_correct GK.generate_correct GK.generate_ct generate_implies

end VG.Proof.Dsa.PPC64LE
