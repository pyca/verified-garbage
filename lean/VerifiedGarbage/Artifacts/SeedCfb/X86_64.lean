module

public import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
public import VerifiedGarbage.Proof.Seed.X86_64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Seed.X86_64.FbFinalLit

/-! # SEED-CFB128 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncrypt
    stack := 1552
    verified := Proof.Seed.X86_64.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecrypt
    stack := 1552
    verified := Proof.Seed.X86_64.cfbDecrypt_framed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbEncryptFinal
    stack := 1552
    verified := Proof.Seed.X86_64.cfbEncryptFinal_framed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cfbDecryptFinal
    stack := 1552
    verified := Proof.Seed.X86_64.cfbDecryptFinal_framed }]

end VG.Artifacts.SeedCfb.X86_64
