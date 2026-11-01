module

import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCT
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtImplies
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_rsa_private_crt` on PPC64LE: verified against the shared contract

`fnContract` states the shared contract on the registers and the stack
(`crt_implies`); with correctness (`fn_correct`) and constant time
(`fn_ct`), `crt` is verified (`crt_verified`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE.Crt

/-- `vg_rsa_private_crt`. -/
theorem crt_verified : Verified target crt (Proof.Rsa.privateCrtContract abi) :=
  Verified.of_correct fn_correct fn_ct crt_implies

end VG.Proof.Bignum.PPC64LE.Crt
