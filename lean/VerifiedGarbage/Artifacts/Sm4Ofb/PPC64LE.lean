module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofb
    stack := 3296
    verified := Proof.Sm4.PPC64LE.ofb_framed Proof.Sm4.PPC64LE.Modes.ofb_verified },
  Spec.Sm4.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ofbFinal
    stack := 3296
    verified := Proof.Sm4.PPC64LE.FbFinal.ofbFinal_framed }]

end VG.Artifacts.Sm4Ofb.PPC64LE
