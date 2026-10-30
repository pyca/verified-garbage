module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cbcEncryptChained
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cbcEnc_framed Proof.TripleDes.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.TripleDes.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cbcDecryptChained
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cbcDec_framed Proof.TripleDes.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.TripleDesCbc.PPC64LE
