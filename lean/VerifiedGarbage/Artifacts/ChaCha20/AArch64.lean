module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Scrub
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64

/-! # ChaCha20 (RFC 8439) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.AArch64

def direct : List Artifact := [
  Spec.ChaCha20.initApi.artifact AArch64.target {
    code := Proof.ChaCha20.AArch64.Stream.initCleared
    verified := .scrubbed ⟨Proof.ChaCha20.AArch64.Stream.initCleared_verified,
      Proof.ChaCha20.AArch64.Stream.initCleared_noResidue _⟩ },
  Spec.ChaCha20.setNonceApi.artifact AArch64.target {
    code := Proof.ChaCha20.AArch64.Stream.setNonceCleared
    verified := .scrubbed ⟨Proof.ChaCha20.AArch64.Stream.setNonceCleared_verified,
      Proof.ChaCha20.AArch64.Stream.setNonceCleared_noResidue _⟩ }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.ChaCha20Xor.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.ChaCha20.AArch64.XorImpl // v ∈ VG.Proof.Variants.ChaCha20Xor.AArch64.variants }) => [
    Spec.ChaCha20.applyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.callee.suffix
      code := Impl.ChaCha20.AArch64.Stream.apply v.1.callee
      verified := Proof.ChaCha20.AArch64.Stream.apply_verified v.1 }
      (AArch64.ScrubAll.clearUnion Proof.ChaCha20.AArch64.Stream.Scrub.applyOwn v.1.clear)
      (Proof.ChaCha20.AArch64.Stream.Scrub.applyOk 0)
      (Proof.ChaCha20.AArch64.Stream.Scrub.applySide v.1 v.2))])

end VG.Artifacts.ChaCha20.AArch64
