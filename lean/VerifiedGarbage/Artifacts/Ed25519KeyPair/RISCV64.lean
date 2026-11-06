module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.KeyPair
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # Ed25519 key-pair derivation from the seed on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519KeyPair.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.keyPairApi.artifact RISCV64.target {
    consts := Impl.Ed25519.RISCV64.combConsts
    code := Impl.Ed25519.RISCV64.KeyPair.keyPair Spec.Sha512.digest512Api.name
      Proof.Ed25519.RISCV64.KeyPair.dgCode "vg_ed25519_public_key_expanded"
      Impl.Ed25519.RISCV64.Whole.publicKeyExpandedCode
    stack := 480
    verified := Proof.Ed25519.RISCV64.KeyPair.verified }]

end VG.Artifacts.Ed25519KeyPair.RISCV64
