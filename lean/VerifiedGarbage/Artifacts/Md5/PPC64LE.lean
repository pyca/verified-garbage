module

public import VerifiedGarbage.Proof.Md5.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # MD5 (RFC 1321) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Md5.PPC64LE

def artifacts : List Artifact := [
  Spec.Md5.initApi.artifact PPC64LE.target {
    code := Impl.Md5.PPC64LE.Stream.init
    verified := Proof.Md5.PPC64LE.Shared.init },
  Spec.Md5.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r7 Impl.Md5.PPC64LE.Stream.update
    stack := 48 + 144
    verified := Proof.Md5.PPC64LE.Shared.update },
  Spec.Md5.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.Md5.PPC64LE.Stream.finalize
    stack := 48 + 144
    verified := Proof.Md5.PPC64LE.Shared.finalize }]

end VG.Artifacts.Md5.PPC64LE
