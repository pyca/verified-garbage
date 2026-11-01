module

public import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86_64.Verified
public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.Lit

/-! # SM4 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rdx 392 Impl.Sm4.X86_64.expandKey
    stack := 3144
    verified := Proof.Sm4.X86_64.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .encrypt)
    stack := 3144
    verified := Proof.Sm4.X86_64.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3144 .rcx 392 (Impl.Sm4.X86_64.ecb .decrypt)
    stack := 3144
    verified := Proof.Sm4.X86_64.ecb_framed .decrypt }]

end VG.Artifacts.Sm4.X86_64
