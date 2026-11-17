module

public import VerifiedGarbage.Proof.Sm3.AArch64.Shared
public import VerifiedGarbage.Proof.Variants.Sm3Compress.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM3 (GB/T 32905-2016) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm3.AArch64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact AArch64.target {
    code := Impl.Sm3.AArch64.Stream.init
    verified := Proof.Sm3.AArch64.Shared.init
    residue := some ⟨Proof.Sm3.AArch64.Stream.init_noResidue _ _⟩ }] ++
  (Proof.Variants.Sm3Compress.AArch64.variants.flatMap fun (v : Proof.Sm3.AArch64.Compress) => [
    Spec.Sm3.updateApi.artifact AArch64.target {
      code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 v.update
      verified := Proof.Sm3.AArch64.Shared.update v
      suffix := v.suffix },
    Spec.Sm3.finalizeApi.artifact AArch64.target {
      code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 v.finalize
      verified := Proof.Sm3.AArch64.Shared.finalize v
      suffix := v.suffix }])

end VG.Artifacts.Sm3.AArch64
