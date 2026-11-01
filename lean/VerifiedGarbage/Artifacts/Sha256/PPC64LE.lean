module

public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared

/-! # SHA-256 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha256.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha256.initApi.artifact PPC64LE.target {
    code := Impl.Sha256.PPC64LE.Stream.init
    verified := Proof.Sha256.PPC64LE.Shared.init },
  Spec.Sha256.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r7 Impl.Sha256.PPC64LE.Stream.update
    stack := 688
    verified := Proof.Sha256.PPC64LE.Shared.update },
  Spec.Sha256.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize
    stack := 688
    verified := Proof.Sha256.PPC64LE.Shared.finalize }]

end VG.Artifacts.Sha256.PPC64LE
