module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit

/-! # Triple DES-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbEncrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfbDecrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.TripleDesCfb.X86_64
