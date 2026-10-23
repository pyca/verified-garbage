module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# BLAKE2 compression function on PPC64LE: the contract

The contract the streaming functions use for their calls of the compression
function; the artifacts' contract is the shared one of
`Spec/Blake2/Contract.lean`, which implies it.
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.PPC64LE VG.Spec.Blake2

/-- PPC64LE contract for `compress(state = r3, blocks = r4, n = r5, t = r6,
last = r7, scratch = r8)`: updates the state at `state` with the `n` blocks at
`blocks`, block `i` with the counter `t + bb · i` and the final block flag if
the low word of `last` is not zero. It reads the blocks and reads and writes
the state and 512 bytes of scratch space, which do not overlap each other.
The pointers, `n`, `t` and `last` are public. -/
def compressPPC64LE {w : Nat} (P : Params w) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 8 * (w / 8)⟩
    let blocks : Region := ⟨s.gpr .r4, blockBytes w * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 512⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' := stateAt w s'.mem (s.gpr .r3) =
    compressBlocks P (stateAt w s.mem (s.gpr .r3)) s.mem (s.gpr .r4) (s.gpr .r5).toNat
      (s.gpr .r6).toNat ((s.gpr .r7).setWidth 32 != 0)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ (s₁.gpr .r7).setWidth 32 = (s₂.gpr .r7).setWidth 32 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp

end VG.Proof.Blake2
