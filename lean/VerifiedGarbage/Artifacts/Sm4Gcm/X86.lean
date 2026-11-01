module

public import VerifiedGarbage.Proof.Sm4.X86.Ctr32Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Frame
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit

/-! # SM4-GCM on baseline x86 (32-bit): its key setup -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.X86

def artifacts : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch 2576 2 Impl.Sm4Gcm.X86.init
    stack := 4112
    verified := Proof.Sm4Gcm.X86.init_framed
    spSafe := Proof.AesGcm.X86.withStackScratch_spSafe Proof.Sm4Gcm.X86.init_spSafe }]

end VG.Artifacts.Sm4Gcm.X86
