module

public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # CAST5-CFB64 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.X86_64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cfbEncrypt
    stack := 240
    verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.X86_64.cfbEncrypt_framed },
  Spec.Cast5.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 Impl.Cast5.X86_64.cfbDecrypt
    stack := 240
    verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.X86_64.cfbDecrypt_framed }]

end VG.Artifacts.Cast5Cfb.X86_64
