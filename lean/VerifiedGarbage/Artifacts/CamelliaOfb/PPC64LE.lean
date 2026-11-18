module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit

/-! # Camellia-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.ofbReg,
  Spec.Camellia.ofbFinalApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.ofbFinalReg]

end VG.Artifacts.CamelliaOfb.PPC64LE
