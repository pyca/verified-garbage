module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P521.PPC64LE.Law

/-! # ECDH over P-521 (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact PPC64LE.target (Proof.Ecdh.PPC64LE.Scrub.p521Exchange hasLaw.law)]

end VG.Artifacts.EcdhP521.PPC64LE
