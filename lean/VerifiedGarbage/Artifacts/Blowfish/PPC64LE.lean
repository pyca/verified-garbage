module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Blowfish.PPC64LE

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 64 .r6 4 Impl.Blowfish.PPC64LE.expandKey
    stack := 64
    verified := Proof.Blowfish.PPC64LE.expandKey_framed },
  Spec.Blowfish.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.encrypt
    stack := 288
    verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 288 .r6 4 Impl.Blowfish.PPC64LE.decrypt
    stack := 288
    verified := Proof.Blowfish.PPC64LE.ecb_framed Proof.Blowfish.PPC64LE.decrypt_verified }]

end VG.Artifacts.Blowfish.PPC64LE
