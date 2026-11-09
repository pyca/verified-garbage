module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Law

/-! # ECDH over brainpoolP512r1 (SP 800-56A §5.7.1.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP512r1.PPC64LE

open VG.Proof.BrainpoolP512r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.exchangeBrainpoolP512r1
    verified := Proof.Ecdh.PPC64LE.BrainpoolP512r1.ecdh_verified hasLaw.law }]

end VG.Artifacts.EcdhBrainpoolP512r1.PPC64LE
