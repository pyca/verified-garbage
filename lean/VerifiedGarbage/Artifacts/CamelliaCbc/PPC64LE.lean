module

public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit

/-! # Camellia-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcEncryptChained
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cbcEnc_framed Proof.Camellia.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Camellia.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 Impl.Camellia.PPC64LE.cbcDecryptChained
    stack := 3408
    verified := Proof.Camellia.PPC64LE.cbcDec_framed Proof.Camellia.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.CamelliaCbc.PPC64LE
