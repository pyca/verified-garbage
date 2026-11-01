module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Implies
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Correct
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.CT
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # `vg_rsa_keygen_key` on PPC64LE: verified against the shared contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG VG.PPC64LE

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [InvLaw] :
    Verified target VG.Impl.RsaKeyGen.PPC64LE.Key.code (Spec.RsaKeyGen.keyContract abi) :=
  Verified.of_correct key_correct key_ct key_implies

end VG.Proof.RsaKeyGen.PPC64LE.Key
