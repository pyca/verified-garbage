module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Verified
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit

/-! # SM4-GCM on baseline x86-64: its counter mode and key setup -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.ctr32Api.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.ctr32
    stack := 3216
    verified := Proof.Sm4.X86_64.ctr32_framed },
  Spec.Sm4.Gcm.initApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rdx Impl.Sm4Gcm.X86_64.init
    stack := 5792
    verified := Proof.Sm4Gcm.X86_64.init_framed
    spSafe := X86_64.withStackScratch_spSafe_of Proof.Sm4Gcm.X86_64.init_spSafe }]

end VG.Artifacts.Sm4Gcm.X86_64
