module

public import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
public import VerifiedGarbage.Proof.Sm4.X86.Verified
public import VerifiedGarbage.Proof.Sm4.X86.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.Lit

/-! # SM4 on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4.X86

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1448 2 358 Impl.Sm4.X86.expandKey
    verified := .unscrubbed Proof.Sm4.X86.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .encrypt)
    verified := .unscrubbed (Proof.Sm4.X86.ecb_framed .encrypt) },
  Spec.Sm4.ecbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (Impl.Sm4.X86.ecb .decrypt)
    verified := .unscrubbed (Proof.Sm4.X86.ecb_framed .decrypt) }]

end VG.Artifacts.Sm4.X86
