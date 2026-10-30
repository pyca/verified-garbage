module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.CtrLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-CTR artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.ctr
    stack := 3296
    verified := Proof.Sm4.PPC64LE.Modes.ctr_framed }]

end VG.Artifacts.Sm4Ctr.PPC64LE
