module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit

/-! # Triple DES-CFB8 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Encrypt
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cfb8Enc_framed Proof.TripleDes.PPC64LE.Modes.cfb8Encrypt_verified },
  Spec.TripleDes.cfb8DecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfb8Decrypt
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cfb8Dec_framed Proof.TripleDes.PPC64LE.Modes.cfb8Decrypt_verified }]

end VG.Artifacts.TripleDesCfb8.PPC64LE
