module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit

/-! # Blowfish-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.ofbReg,
  Spec.Blowfish.ofbFinalApi.artifact PPC64LE.target Proof.Blowfish.PPC64LE.Scrub.ofbFinalReg]

end VG.Artifacts.BlowfishOfb.PPC64LE
