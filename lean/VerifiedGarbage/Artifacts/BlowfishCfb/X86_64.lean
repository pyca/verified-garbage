module

public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

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
    verified := Proof.Blowfish.X86_64.cfbDecrypt_framed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbEncryptFinal
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbEncryptFinal_framed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cfbDecryptFinal
    stack := 96
    verified := Proof.Blowfish.X86_64.cfbDecryptFinal_framed }]

end VG.Artifacts.BlowfishCfb.X86_64
