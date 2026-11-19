module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Scrub

/-! # Ed25519 (RFC 8032) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ed25519.RISCV64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ "_core")
      Proof.Ed25519.RISCV64.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode
    verified := Proof.Ed25519.RISCV64.KeyPair.verified }
    (Proof.Ed25519.RISCV64.Scrub.keyPairOut Impl.Ed25519.RISCV64.combConsts _)),
  Spec.Ed25519.signExpandedApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ed25519.RISCV64.Whole.signExpandedCode
    verified := Proof.Ed25519.RISCV64.Whole.signExpanded_framed }
    (Proof.Ed25519.RISCV64.Scrub.signExpandedOut Impl.Ed25519.RISCV64.combConsts _)),
  Spec.Ed25519.verifyApi.artifact RISCV64.target (RISCV64.Scrub.withScrub {
    code := Impl.Ed25519.RISCV64.Whole.verifyCode
    verified := Proof.Ed25519.RISCV64.Whole.verify_framed }
    (Proof.Ed25519.RISCV64.Scrub.verifyOut Impl.Ed25519.RISCV64.bConsts _))]

end VG.Artifacts.Ed25519.RISCV64
