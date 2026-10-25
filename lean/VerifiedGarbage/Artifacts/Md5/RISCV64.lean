module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Md5.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# MD5 (RFC 1321) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.Md5.RISCV64

def artifacts : List Artifact := [
  Spec.Md5.compressApi.artifact RISCV64.target {
    notes := ["The MD buffer and the blocks are read and written a byte at a time, since the \
        contract states no alignment for them; `scratch` is not used."]
    code := Impl.Md5.RISCV64.compress
    verified := Proof.Md5.RISCV64.Shared.compress },
  Spec.Md5.initApi.artifact RISCV64.target {
    code := Impl.Md5.RISCV64.Stream.init
    verified := Proof.Md5.RISCV64.Shared.init },
  Spec.Md5.updateApi.artifact RISCV64.target {
    notes := ["Keeps its working space, and the registers it saves, in a frame of 144 bytes on the \
        stack."]
    code := Impl.Md5.RISCV64.Stream.update
    stack := 144
    verified := Proof.Md5.RISCV64.Shared.update },
  Spec.Md5.finalizeApi.artifact RISCV64.target {
    notes := ["Keeps its working space, and the registers it saves, in a frame of 144 bytes on the \
        stack."]
    code := Impl.Md5.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Md5.RISCV64.Shared.finalize }]

end VG.Artifacts.Md5.RISCV64
