import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7 -/

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := Arm.target
    doc := Spec.Sha512.compressApi.doc
    code := Impl.Sha512.Arm.compress
    contract := Spec.Sha512.compressContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init384Api with
    target := Arm.target
    doc := Spec.Sha512.init384Api.doc
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512Api with
    target := Arm.target
    doc := Spec.Sha512.init512Api.doc
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_224Api with
    target := Arm.target
    doc := Spec.Sha512.init512_224Api.doc
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init512_256Api with
    target := Arm.target
    doc := Spec.Sha512.init512_256Api.doc
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.updateApi with
    target := Arm.target
    doc := Spec.Sha512.updateApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 1392 2 Impl.Sha512.Arm.Stream.update
    contract := Spec.Sha512.updateContract Arm.abi 1392
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalizeApi with
    target := Arm.target
    doc := Spec.Sha512.finalizeApi.doc
    code := Impl.StackScratch.Arm.withStackScratch 1392 1 Impl.Sha512.Arm.Stream.finalize
    contract := Spec.Sha512.finalizeContract Arm.abi 1392
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.updateScratchApi with
    target := Arm.target
    doc := Spec.Sha512.updateScratchApi.doc
    code := Impl.Sha512.Arm.Stream.update
    contract := Spec.Sha512.updateScratchContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.updateScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalizeScratchApi with
    target := Arm.target
    doc := Spec.Sha512.finalizeScratchApi.doc
    code := Impl.Sha512.Arm.Stream.finalize
    contract := Spec.Sha512.finalizeScratchContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.finalizeScratch
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalize384Api with
    target := Arm.target
    doc := Spec.Sha512.finalize384Api.doc
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384)
    contract := Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 1392
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize384
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalize512_256Api with
    target := Arm.target
    doc := Spec.Sha512.finalize512_256Api.doc
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256)
    contract := Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 1392
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize512_256
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalize512_224Api with
    target := Arm.target
    doc := Spec.Sha512.finalize512_224Api.doc
    code := Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224)
    contract := Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 1392
    stack := 1392
    verified := Proof.Sha512.Arm.Shared.finalize512_224
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha512.Arm
