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
    verified := Proof.Sha256.RISCV64.Shared.compress }]

end VG.Artifacts.Sha256.RISCV64
