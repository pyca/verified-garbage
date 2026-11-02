module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdContract
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCorrect
import VerifiedGarbage.Proof.Rsa.PPC64LE.RdCT

/-! # `vg_rsa_recover_primes_det` on PPC64LE: verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.RecDet

open VG VG.PPC64LE

/-- `vg_rsa_recover_primes_det`. -/
theorem rd_verified [VG.Proof.Rsa.PPC64LE.InvLaw] :
    Verified target VG.Impl.Rsa.PPC64LE.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct rd_correct rd_ct VG.Proof.Rsa.PPC64LE.Recover.rd_implies

end VG.Proof.Rsa.PPC64LE.RecDet
