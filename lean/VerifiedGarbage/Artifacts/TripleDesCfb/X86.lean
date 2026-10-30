module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB64 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt
    stack := 984
    verified := Proof.TripleDes.X86.Fb.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecrypt
    stack := 984
    verified := Proof.TripleDes.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.TripleDesCfb.X86
