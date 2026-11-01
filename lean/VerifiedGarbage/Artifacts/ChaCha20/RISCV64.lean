module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Shared
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.ApplyCT
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ChaCha20 (RFC 8439) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.ChaCha20.RISCV64

def artifacts : List Artifact := [
  Spec.ChaCha20.initApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Stream.init
    verified := Proof.ChaCha20.RISCV64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Stream.setNonce
    verified := Proof.ChaCha20.RISCV64.Stream.setNonce_verified },
  Spec.ChaCha20.applyApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Stream.apply
    verified := Proof.ChaCha20.RISCV64.Stream.apply_verified }]

end VG.Artifacts.ChaCha20.RISCV64
