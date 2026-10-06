import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.KeyImplies

/-!
# `vg_rsa_check_key` on x86-64: verified against the shared contract

Correct (`keyCode_correct`), constant time (`keyCode_constantTime`), and the
contract on the registers and the stack implies the shared one
(`key_implies`).
-/

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CheckKey

/-- `vg_rsa_check_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem key_verified (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct (keyCode_correct hmx) keyCode_constantTime key_implies

end VG.Proof.Rsa.X86_64.Key
