module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Verified
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Lit

/-! # Triple DES on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.TripleDes.PPC64LE

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact PPC64LE.target {
    code := Impl.TripleDes.PPC64LE.Key.expandKey
    verified := Proof.TripleDes.PPC64LE.Key.verified },
  Spec.TripleDes.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128
      Impl.TripleDes.PPC64LE.Bitslice.encrypt
    stack := 1056
    verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Bitsliced.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1056 .r6 128
      Impl.TripleDes.PPC64LE.Bitslice.decrypt
    stack := 1056
    verified := Proof.TripleDes.PPC64LE.ecb_framed Proof.TripleDes.PPC64LE.Bitsliced.decrypt_verified }]

end VG.Artifacts.TripleDes.PPC64LE
