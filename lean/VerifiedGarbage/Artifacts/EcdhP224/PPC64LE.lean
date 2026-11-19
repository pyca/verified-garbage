module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P224.PPC64LE.Law

/-! # ECDH over P-224 (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact PPC64LE.target (Proof.Ecdh.PPC64LE.Scrub.p224Exchange hasLaw.law)]

end VG.Artifacts.EcdhP224.PPC64LE
