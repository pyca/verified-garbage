module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.VerifiedBlock
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Triple DES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Key.expandKey
    verified := Proof.TripleDes.PPC64LE.Key.verified },
  Spec.TripleDes.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128
      Impl.TripleDes.PPC64LE.Ecb.encrypt
    stack := 1056
    verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Ecb.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128
      Impl.TripleDes.PPC64LE.Ecb.decrypt
    stack := 1056
    verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Ecb.decrypt_verified }]

end VG.Artifacts.TripleDes.PPC64LE
