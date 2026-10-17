module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower

/-!
# The scalar round with its temporary lanes in memory

`lowerMem off` is `lower` with the two temporary lanes of theta kept in the
two words at `[x30, #off]` and `[x30, #off + 8]` rather than in v24/v25:
the round then writes no vector register, so it can be interleaved with
code that holds its state in all of them (`Impl/Sha3/AArch64/Hybrid.lean`).
`x30` is free during the rounds (the boundary keeps the state's pointer
elsewhere).
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- The temporary lanes in the words at `[x30, #off + 8 k]`. -/
def lowerMem (off : Nat) : ScalarOp → List Instr
  | .spill k a => [.str .x a .x30 (off + 8 * k)]
  | .reload d k => [.ldr .x d .x30 (off + 8 * k)]
  | op => lower op

/-- One round through chi with the temporary lanes at `[x30, #off]`. -/
def memCoreInstrs (off : Nat) : List Instr := coreOps.flatMap (lowerMem off)

end VG.Impl.Sha3.AArch64.Scalar
