module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86.FbFinalVerified
import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
    stack := 2772
    verified := Proof.Camellia.X86.Fb.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
    stack := 2772
    verified := Proof.Camellia.X86.Fb.cfbDecrypt_framed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncryptFinal
    stack := 2772
    verified := Proof.Camellia.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecryptFinal
    stack := 2772
    verified := Proof.Camellia.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.CamelliaCfb.X86
