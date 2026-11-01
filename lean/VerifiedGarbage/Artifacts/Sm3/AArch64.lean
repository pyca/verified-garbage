module

public import VerifiedGarbage.Proof.Sm3.AArch64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SM3 (GB/T 32905-2016) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm3.AArch64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact AArch64.target {
    code := Impl.Sm3.AArch64.Stream.init
    verified := Proof.Sm3.AArch64.Shared.init },
  Spec.Sm3.updateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Sm3.AArch64.Stream.update
    stack := 16 + 112
    verified := Proof.Sm3.AArch64.Shared.update },
  Spec.Sm3.finalizeApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Sm3.AArch64.Stream.finalize
    stack := 16 + 112
    verified := Proof.Sm3.AArch64.Shared.finalize }]

end VG.Artifacts.Sm3.AArch64
