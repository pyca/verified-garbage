module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.PPC64LE.Law

/-! # ECDH over brainpoolP384r1 (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP384r1.PPC64LE

open VG.Proof.BrainpoolP384r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP384r1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.brainpoolp384r1Exchange
    verified := Proof.Ecdh.PPC64LE.Scrub.brainpoolp384r1Exchange_scrubbed hasLaw.law }]

end VG.Artifacts.EcdhBrainpoolP384r1.PPC64LE
