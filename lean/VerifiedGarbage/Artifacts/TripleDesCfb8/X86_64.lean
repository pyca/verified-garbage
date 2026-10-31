module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit

/-! # Triple DES-CFB8 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Encrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Encrypt_framed },
  Spec.TripleDes.cfb8DecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 Impl.TripleDes.X86_64.cfb8Decrypt
    stack := 984
    verified := Proof.TripleDes.X86_64.cfb8Decrypt_framed }]

end VG.Artifacts.TripleDesCfb8.X86_64
