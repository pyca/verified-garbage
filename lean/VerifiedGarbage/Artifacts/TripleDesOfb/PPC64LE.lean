module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.ofb
    stack := 608
    verified := Proof.TripleDes.PPC64LE.ofb_framed Proof.TripleDes.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.TripleDesOfb.PPC64LE
