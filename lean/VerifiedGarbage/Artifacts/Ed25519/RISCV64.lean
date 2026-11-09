module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ExpandedVerified
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgVerified

/-! # Ed25519 (RFC 8032) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.RISCV64.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode
    stack := 480
    verified := Proof.Ed25519.RISCV64.KeyPair.verified },
  Spec.Ed25519.signExpandedApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Whole.signExpandedCode
    stack := 496
    verified := Proof.Ed25519.RISCV64.Whole.signExpanded_framed },
  Spec.Ed25519.verifyApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.Whole.verifyCode
    stack := 480
    verified := Proof.Ed25519.RISCV64.Whole.verify_framed }]

end VG.Artifacts.Ed25519.RISCV64
