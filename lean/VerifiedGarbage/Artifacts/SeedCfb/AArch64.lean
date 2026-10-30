module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEED-CFB128 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.AArch64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cfbEncrypt_framed },
  Spec.Seed.cfbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecrypt
    stack := 1456
    verified := Proof.Seed.AArch64.cfbDecrypt_framed }]

end VG.Artifacts.SeedCfb.AArch64
