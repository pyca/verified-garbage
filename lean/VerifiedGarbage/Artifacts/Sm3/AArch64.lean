module

public import VerifiedGarbage.Proof.Sm3.AArch64.Shared
public import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Init
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
  (Proof.Variants.Sm3Compress.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Sm3.AArch64.Compress // v ∈ Proof.Variants.Sm3Compress.AArch64.variants }) => [
    Spec.Sm3.updateApi.artifact AArch64.target (Proof.Sm3.AArch64.Shared.updateReg v.1 v.2),
    Spec.Sm3.finalizeApi.artifact AArch64.target (Proof.Sm3.AArch64.Shared.finalizeReg v.1 v.2)])

end VG.Artifacts.Sm3.AArch64
