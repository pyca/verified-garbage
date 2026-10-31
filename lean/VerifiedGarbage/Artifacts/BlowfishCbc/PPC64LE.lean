module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.PPC64LE.ModesLit

/-! # Blowfish-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcEncryptChained
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cbcEnc_framed Proof.Blowfish.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Blowfish.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 Impl.Blowfish.PPC64LE.cbcDecryptChained
    stack := 128
    verified := Proof.Blowfish.PPC64LE.cbcDec_framed Proof.Blowfish.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.BlowfishCbc.PPC64LE
