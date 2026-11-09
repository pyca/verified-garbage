module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P521.Lit
public import VerifiedGarbage.Proof.P521.PPC64LE.Law

/-! # ECDH over P-521 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP521
    verified := Proof.Ecdh.PPC64LE.P521.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP521.PPC64LE
