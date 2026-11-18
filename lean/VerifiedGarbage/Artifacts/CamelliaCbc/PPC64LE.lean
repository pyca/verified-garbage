module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CBC on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cbcEncReg,
  Spec.Camellia.cbcDecryptChainedApi.artifact PPC64LE.target Proof.Camellia.PPC64LE.Scrub.cbcDecReg]

end VG.Artifacts.CamelliaCbc.PPC64LE
