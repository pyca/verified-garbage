module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit

/-! # SM4-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcEncryptChained
    stack := 3296
    verified := Proof.Sm4.PPC64LE.cbcEnc_framed Proof.Sm4.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Sm4.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 Impl.Sm4.PPC64LE.cbcDecryptChained
    stack := 3296
    verified := Proof.Sm4.PPC64LE.cbcDec_framed Proof.Sm4.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.Sm4Cbc.PPC64LE
