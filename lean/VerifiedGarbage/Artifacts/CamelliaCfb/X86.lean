module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86.FbFinalVerified
import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit

/-! # Camellia-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.X86

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncrypt
    verified := .unscrubbed Proof.Camellia.X86.Fb.cfbEncrypt_framed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecrypt
    verified := .unscrubbed Proof.Camellia.X86.Fb.cfbDecrypt_framed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbEncryptFinal
    verified := .unscrubbed Proof.Camellia.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cfbDecryptFinal
    verified := .unscrubbed Proof.Camellia.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.CamelliaCfb.X86
