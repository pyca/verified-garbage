module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# BLAKE2 compression function on RISC-V: the contract

The contract the streaming functions use for their calls of the compression
function; the artifacts' contract is the shared one of
`Spec/Blake2/Contract.lean`, which implies it.
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.RISCV64 VG.Spec.Blake2

/-- RISC-V contract for `compress(state = a0, blocks = a1, n = a2, t = a3,
last = a4, scratch = a5)`: updates the state at `state` with the `n` blocks at
`blocks`, block `i` with the counter `t + bb · i` and the final block flag if
the low word of `last` is not zero. It reads the blocks and reads and writes
the state and 512 bytes of scratch space, which do not overlap each other.
The pointers, `n`, `t` and `last` are public. -/
def compressRISCV64 {w : Nat} (P : Params w) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 8 * (w / 8)⟩
    let blocks : Region := ⟨s.gpr .a1, blockBytes w * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 512⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' := stateAt w s'.mem (s.gpr .a0) =
    compressBlocks P (stateAt w s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
      (s.gpr .a3).toNat ((s.gpr .a4).setWidth 32 != 0)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ (s₁.gpr .a4).setWidth 32 = (s₂.gpr .a4).setWidth 32 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

end VG.Proof.Blake2
