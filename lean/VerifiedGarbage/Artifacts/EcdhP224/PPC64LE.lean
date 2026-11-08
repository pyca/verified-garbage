module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.P224.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Lit
public import VerifiedGarbage.Proof.P224.PPC64LE.Law

/-! # ECDH over P-224 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeP224
    verified := Proof.Ecdh.PPC64LE.P224.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhP224.PPC64LE
