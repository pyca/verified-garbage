module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Blowfish.PPC64LE.FbFinalLit

/-! # Blowfish-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofb
    stack := 128
    verified := Proof.Blowfish.PPC64LE.ofb_framed Proof.Blowfish.PPC64LE.Modes.ofb_verified },
  Spec.Blowfish.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.ofbFinal
    stack := 128
    verified := Proof.Blowfish.PPC64LE.FbFinal.ofbFinal_framed }]

end VG.Artifacts.BlowfishOfb.PPC64LE
