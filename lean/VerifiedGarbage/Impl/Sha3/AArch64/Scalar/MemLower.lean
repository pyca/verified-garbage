module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower

/-!
# The scalar round with its temporary lanes in memory

`lowerMem off` is `lower` with the two temporary lanes of theta kept in the
two words at `[sp, #off]` and `[sp, #off + 8]` (in a frame) rather than in
v24/v25: the round then writes no vector register, so it can be
interleaved with code that holds its state in all of them. The round uses
every general register (`x30` among them), so the words are addressed from
the stack pointer.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- The temporary lanes in the words at `[sp, #off + 8 k]`. -/
def lowerMem (off : Nat) : ScalarOp → List Instr
  | .spill k a => [.strSp a (off + 8 * k)]
  | .reload d k => [.ldrSp d (off + 8 * k)]
  | op => lower op

/-- One round through chi with the temporary lanes at `[sp, #off]`. -/
def memCoreInstrs (off : Nat) : List Instr := coreOps.flatMap (lowerMem off)

end VG.Impl.Sha3.AArch64.Scalar
