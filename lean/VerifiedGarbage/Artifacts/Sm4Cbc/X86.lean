module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.CbcLit

/-! # SM4-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cbcEncryptChained
    verified := Proof.Sm4.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cbcDecryptChained
    verified := Proof.Sm4.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Sm4Cbc.X86
