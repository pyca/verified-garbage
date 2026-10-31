module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.FbLit

/-! # SEED-CFB128 artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbEncrypt
    stack := 1188
    verified := Proof.Seed.X86.Fb.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cfbDecrypt
    stack := 1188
    verified := Proof.Seed.X86.Fb.cfbDecrypt_framed }]

end VG.Artifacts.SeedCfb.X86
