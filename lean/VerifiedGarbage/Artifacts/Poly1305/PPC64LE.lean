module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Poly1305 (RFC 8439 §2.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Poly1305.PPC64LE

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact PPC64LE.target Proof.Poly1305.PPC64LE.Scrub.initReg,
  Spec.Poly1305.updateApi.artifact PPC64LE.target Proof.Poly1305.PPC64LE.Scrub.updateReg,
  Spec.Poly1305.finalizeApi.artifact PPC64LE.target Proof.Poly1305.PPC64LE.Scrub.finalizeReg]

end VG.Artifacts.Poly1305.PPC64LE
