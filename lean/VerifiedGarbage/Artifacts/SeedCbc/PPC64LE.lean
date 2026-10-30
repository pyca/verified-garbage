module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.ModesLit

/-! # SEED-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcEncryptChained
    stack := 1184
    verified := Proof.Seed.PPC64LE.cbcEnc_framed Proof.Seed.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Seed.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 Impl.Seed.PPC64LE.cbcDecryptChained
    stack := 1184
    verified := Proof.Seed.PPC64LE.cbcDec_framed Proof.Seed.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.SeedCbc.PPC64LE
