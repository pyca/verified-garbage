module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Seed.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Seed.X86.FbFinalLit

/-! # SEED-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncrypt
    verified := Proof.Seed.X86.Fb.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecrypt
    verified := Proof.Seed.X86.Fb.cfbDecrypt_framed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncryptFinal
    verified := Proof.Seed.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecryptFinal
    verified := Proof.Seed.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.SeedCfb.X86
