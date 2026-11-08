module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FbFinalLit

/-! # Triple DES-CFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncrypt
    stack := 608
    verified := Proof.TripleDes.PPC64LE.cfbEnc_framed Proof.TripleDes.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.TripleDes.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1632 .r7 200 Impl.TripleDes.PPC64LE.cfbDecrypt
    stack := 1632
    verified := Proof.TripleDes.PPC64LE.cfbDec_framed Proof.TripleDes.PPC64LE.Modes.cfbDecrypt_verified },
  Spec.TripleDes.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbEncryptFinal
    stack := 608
    verified := Proof.TripleDes.PPC64LE.FbFinal.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 Impl.TripleDes.PPC64LE.cfbDecryptFinal
    stack := 608
    verified := Proof.TripleDes.PPC64LE.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.PPC64LE
