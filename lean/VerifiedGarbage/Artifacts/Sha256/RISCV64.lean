module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SHA-256 (FIPS 180-4) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.Sha256.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.compressApi.artifact RISCV64.target {
    notes := ["The hash value and the blocks are read and written a byte at a time, since the \
        contract states no alignment for them; `scratch` is rounded up to a multiple of 8, so \
        that the message schedule in it takes aligned word accesses."]
    code := Impl.Sha256.RISCV64.compress
    verified := Proof.Sha256.RISCV64.Shared.compress },
  Spec.Sha256.initApi.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.init
    verified := Proof.Sha256.RISCV64.Shared.init },
  Spec.Sha256.updateApi.artifact RISCV64.target {
    notes := ["Keeps its working space, and the registers it saves, in a frame of 144 bytes on the \
        stack."]
    code := Impl.Sha256.RISCV64.Stream.update
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.update },
  Spec.Sha256.finalizeApi.artifact RISCV64.target {
    notes := ["Keeps its working space, and the registers it saves, in a frame of 144 bytes on the \
        stack."]
    code := Impl.Sha256.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.finalize }]

end VG.Artifacts.Sha256.RISCV64
