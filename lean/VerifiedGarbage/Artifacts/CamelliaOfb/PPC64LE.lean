module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.PPC64LE.FbFinalLit

/-! # Camellia-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofb
    stack := 3408
    verified := Proof.Camellia.PPC64LE.ofb_framed Proof.Camellia.PPC64LE.Modes.ofb_verified },
  Spec.Camellia.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ofbFinal
    stack := 3408
    verified := Proof.Camellia.PPC64LE.FbFinal.ofbFinal_framed }]

end VG.Artifacts.CamelliaOfb.PPC64LE
