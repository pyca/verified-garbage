module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P384.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P384.Lit
public import VerifiedGarbage.Proof.P384.PPC64LE.Law

/-! # ECDH over P-384 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP384
    verified := Proof.Ecdh.PPC64LE.P384.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP384.PPC64LE
