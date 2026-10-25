module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Permute
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
    verified := Proof.Sha3.RISCV64.permute_verified }]

end VG.Artifacts.Sha3.RISCV64
