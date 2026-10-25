module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Shared
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.ApplyCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ChaCha20 (RFC 8439) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.ChaCha20.RISCV64

def artifacts : List Artifact := [
  Spec.ChaCha20.blockApi.artifact RISCV64.target {
    notes := ["The state is read and the result written a byte at a time, since the contract states \
        no alignment for them; the callee-saved registers the function uses are saved in `buf` at \
        offset 64, rounded up to a multiple of 8."]
    code := Impl.ChaCha20.RISCV64.block
    verified := Proof.ChaCha20.RISCV64.Shared.block },
  Spec.ChaCha20.xorApi.artifact RISCV64.target {
    notes := ["Our caller's registers that the function uses across its calls of \
        `vg_chacha20_block`, and the return address, are saved in `buf` at offset 256, rounded up \
        to a multiple of 8; no stack is used."]
    code := Impl.ChaCha20.RISCV64.Xor.xor
    verified := Proof.ChaCha20.RISCV64.Xor.xor_verified },
  Spec.ChaCha20.initApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Stream.init
    verified := Proof.ChaCha20.RISCV64.Stream.init_verified },
  Spec.ChaCha20.setNonceApi.artifact RISCV64.target {
    code := Impl.ChaCha20.RISCV64.Stream.setNonce
    verified := Proof.ChaCha20.RISCV64.Stream.setNonce_verified },
  Spec.ChaCha20.applyApi.artifact RISCV64.target {
    notes := ["Our caller's registers that the function uses across its calls, and the return \
        address, are saved in the streaming state at offset 576, rounded up to a multiple of 8; no \
        stack is used."]
    code := Impl.ChaCha20.RISCV64.Stream.apply
    verified := Proof.ChaCha20.RISCV64.Stream.apply_verified }]

end VG.Artifacts.ChaCha20.RISCV64
