module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Camellia.PPC64LE.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CTR artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.ctr
    stack := 3408
    verified := Proof.Camellia.PPC64LE.ctr_framed Proof.Camellia.PPC64LE.Modes.ctr_verified },
  Spec.Camellia.ctrFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r8 10 Impl.Camellia.PPC64LE.ctrFinal
    stack := 3520
    verified := Proof.Camellia.PPC64LE.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.CamelliaCtr.PPC64LE
