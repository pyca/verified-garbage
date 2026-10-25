module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Permute
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# SHA-3 and SHAKE (FIPS 202) on RISC-V

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted, each made from its function's `Api` (in `Spec/`, reviewed with the
contract), with the notes on the implementation added here.
-/

@[expose] public section

namespace VG.Artifacts.Sha3.RISCV64

def artifacts : List Artifact := [
  Spec.Sha3.permuteApi.artifact RISCV64.target {
    notes := ["The state is copied a byte at a time into a frame of 608 bytes on the stack, since \
        the contract states no alignment for it, and back; the rounds run on that copy and a \
        second state in the frame, with the round constants and the registers it saves. \
        `scratch` is not used."]
    code := Impl.Sha3.RISCV64.permute
    stack := 608
    verified := Proof.Sha3.RISCV64.permute_verified },
  Spec.Sha3.absorbApi.artifact RISCV64.target {
    notes := ["The state and the data are accessed a byte at a time, since the contract states no \
        alignment for them. Keeps the permutation's scratch space, and the registers it saves, in \
        a frame of 560 bytes on the stack, above the permutation's own frame."]
    code := Impl.Sha3.RISCV64.Stream.absorb
    stack := 1168
    verified := Proof.Sha3.RISCV64.Stream.absorb_verified },
  Spec.Sha3.padApi.artifact RISCV64.target {
    notes := ["Keeps the permutation's scratch space, and the return address, in a frame of 528 bytes \
        on the stack, above the permutation's own frame."]
    code := Impl.Sha3.RISCV64.Stream.pad
    stack := 1136
    verified := Proof.Sha3.RISCV64.Stream.pad_verified },
  Spec.Sha3.squeezeApi.artifact RISCV64.target {
    notes := ["The state and the output are accessed a byte at a time, since the contract states no \
        alignment for them. Keeps the permutation's scratch space, and the registers it saves, in \
        a frame of 560 bytes on the stack, above the permutation's own frame."]
    code := Impl.Sha3.RISCV64.Stream.squeeze
    stack := 1168
    verified := Proof.Sha3.RISCV64.Stream.squeeze_verified }]

end VG.Artifacts.Sha3.RISCV64
