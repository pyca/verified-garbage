module

public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit

/-! # Camellia-CFB128 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecrypt
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecrypt_framed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbEncryptFinal
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbEncryptFinal_framed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cfbDecryptFinal
    stack := 3288
    verified := Proof.Camellia.X86_64.cfbDecryptFinal_framed }]

end VG.Artifacts.CamelliaCfb.X86_64
