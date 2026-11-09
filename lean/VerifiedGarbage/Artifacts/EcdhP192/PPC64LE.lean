module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P192.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P192.Lit
public import VerifiedGarbage.Proof.P192.PPC64LE.Law

/-! # ECDH over P-192 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP192.PPC64LE

open VG.Proof.P192.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP192
    verified := Proof.Ecdh.PPC64LE.P192.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP192.PPC64LE
