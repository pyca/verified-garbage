module

public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncrypt
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecrypt
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.BlowfishCfb.X86_64
