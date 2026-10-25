module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Verified
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-!
# BLAKE2b (RFC 7693) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.Blake2b.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.compressBApi.artifact RISCV64.target {
    notes := ["The state and the blocks are accessed a byte at a time, since the contract states no \
        alignment for them: the hash value and each block are copied to `scratch`, rounded up to a \
        multiple of 8, where the rounds read and write them as aligned words."]
    code := Impl.Blake2.RISCV64.compress Spec.Blake2.b
    verified := Proof.Blake2.RISCV64.compressB_verified },
  Spec.Blake2.initBApi.artifact RISCV64.target {
    notes := ["The state and the key are accessed a byte at a time, since the contract states no \
        alignment for them."]
    code := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b
    verified := Proof.Blake2.RISCV64.Stream.initB_verified },
  Spec.Blake2.updateBApi.artifact RISCV64.target {
    notes := ["`vg_blake2b_update_scratch`, with its working space in a frame of 576 bytes on the \
        stack."]
    code := Impl.Blake2.RISCV64.Stream.update Spec.Blake2.b
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.updateB_verified },
  Spec.Blake2.finalizeBApi.artifact RISCV64.target {
    notes := ["`vg_blake2b_finalize_scratch`, with its working space in a frame of 576 bytes on the \
        stack."]
    code := Impl.Blake2.RISCV64.Stream.finalize Spec.Blake2.b
    stack := 576
    verified := Proof.Blake2.RISCV64.Stream.finalizeB_verified },
  Spec.Blake2.updateBScratchApi.artifact RISCV64.target {
    notes := ["The state and the data are accessed a byte at a time, since the contract states no \
        alignment for them. `scratch`, rounded up to a multiple of 8, holds the compression \
        function's scratch space, then the return address and the registers saved."]
    code := Impl.Blake2.RISCV64.Stream.updateScratch Spec.Blake2.b
    verified := Proof.Blake2.RISCV64.Stream.updateScratchB_verified },
  Spec.Blake2.finalizeBScratchApi.artifact RISCV64.target {
    notes := ["The state and the output are accessed a byte at a time, since the contract states no \
        alignment for them. `scratch`, rounded up to a multiple of 8, holds the compression \
        function's scratch space, then the return address and the registers saved."]
    code := Impl.Blake2.RISCV64.Stream.finalizeScratch Spec.Blake2.b
    verified := Proof.Blake2.RISCV64.Stream.finalizeScratchB_verified }]

end VG.Artifacts.Blake2b.RISCV64
