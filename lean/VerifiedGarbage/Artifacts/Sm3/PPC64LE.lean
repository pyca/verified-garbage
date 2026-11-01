module

public import VerifiedGarbage.Proof.Sm3.PPC64LE.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM3 (GB/T 32905-2016) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sm3.PPC64LE

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact PPC64LE.target {
    code := Impl.Sm3.PPC64LE.Stream.init
    verified := Proof.Sm3.PPC64LE.Shared.init },
  Spec.Sm3.updateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sm3.PPC64LE.Stream.update
    stack := 48 + 192
    verified := Proof.Sm3.PPC64LE.Shared.update },
  Spec.Sm3.finalizeApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sm3.PPC64LE.Stream.finalize
    stack := 48 + 192
    verified := Proof.Sm3.PPC64LE.Shared.finalize }]

end VG.Artifacts.Sm3.PPC64LE
