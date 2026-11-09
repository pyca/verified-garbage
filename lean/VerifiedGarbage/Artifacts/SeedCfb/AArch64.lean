module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit

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
    verified := Proof.Seed.AArch64.cfbDecrypt_framed },
  Spec.Seed.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbEncryptFinal
    stack := 1456
    verified := Proof.Seed.AArch64.cfbEncryptFinal_framed },
  Spec.Seed.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 Impl.Seed.AArch64.cfbDecryptFinal
    stack := 1456
    verified := Proof.Seed.AArch64.cfbDecryptFinal_framed }]

end VG.Artifacts.SeedCfb.AArch64
