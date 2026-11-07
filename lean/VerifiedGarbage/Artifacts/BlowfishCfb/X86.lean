module

public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
public import VerifiedGarbage.Proof.Blowfish.X86.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
import VerifiedGarbage.Proof.Blowfish.X86.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Blowfish-CFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.X86

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncrypt
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbEncrypt_framed },
  Spec.Blowfish.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecrypt
    stack := 112
    verified := Proof.Blowfish.X86.Fb.cfbDecrypt_framed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbEncryptFinal
    stack := 112
    verified := Proof.Blowfish.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 112 4 22 Impl.Blowfish.X86.cfbDecryptFinal
    stack := 112
    verified := Proof.Blowfish.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.BlowfishCfb.X86
