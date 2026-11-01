module

public import VerifiedGarbage.Proof.Sha1.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-1 (FIPS 180-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha1.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact PPC64LE.target {
    code := Impl.Sha1.PPC64LE.Stream.init
    verified := Proof.Sha1.PPC64LE.Shared.init },
  Spec.Sha1.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update
    stack := 48 + 192
    verified := Proof.Sha1.PPC64LE.Shared.update },
  Spec.Sha1.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize
    stack := 48 + 192
    verified := Proof.Sha1.PPC64LE.Shared.finalize }]

end VG.Artifacts.Sha1.PPC64LE
