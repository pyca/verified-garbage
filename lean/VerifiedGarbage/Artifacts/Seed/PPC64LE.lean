module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Frame
public import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit

/-! # SEED artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Seed.PPC64LE

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey
    stack := 1072
    verified := Proof.Seed.PPC64LE.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .encrypt)
    stack := 1168
    verified := Proof.Seed.PPC64LE.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall .decrypt)
    stack := 1168
    verified := Proof.Seed.PPC64LE.ecbCall_framed .decrypt }]

end VG.Artifacts.Seed.PPC64LE
