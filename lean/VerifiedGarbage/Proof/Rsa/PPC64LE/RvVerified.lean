module

import VerifiedGarbage.Proof.Rsa.PPC64LE.RvImplies
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Recover
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # `vg_rsa_recover_primes` on PPC64LE: verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE

/-- `vg_rsa_recover_primes`. -/
theorem rv_verified :
    Verified target VG.Impl.Rsa.PPC64LE.Recover.code (Spec.Rsa.recoverPrimesContract abi) :=
  Verified.of_correct rv_correct rv_ct rv_implies

end VG.Proof.Rsa.PPC64LE.Recover
