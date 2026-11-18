module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CFB8 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfb8EncryptReg,
  Spec.TripleDes.cfb8DecryptApi.artifact PPC64LE.target Proof.TripleDes.PPC64LE.Scrub.cfb8DecryptReg]

end VG.Artifacts.TripleDesCfb8.PPC64LE
