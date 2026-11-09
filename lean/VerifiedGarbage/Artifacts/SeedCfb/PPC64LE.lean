module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit

/-! # SEED-CFB128 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncrypt
    stack := 1184
    verified := Proof.Seed.PPC64LE.cfbEnc_framed Proof.Seed.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Seed.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1424 .r7 174 Impl.Seed.PPC64LE.cfbDecrypt
    stack := 1424
    verified := Proof.Seed.PPC64LE.cfbDec_framed Proof.Seed.PPC64LE.Modes.cfbDecrypt_verified },
  Spec.Seed.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbEncryptFinal
    stack := 1184
    verified := Proof.Seed.PPC64LE.FbFinal.cfbEncryptFinal_framed },
  Spec.Seed.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cfbDecryptFinal
    stack := 1184
    verified := Proof.Seed.PPC64LE.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.SeedCfb.PPC64LE
