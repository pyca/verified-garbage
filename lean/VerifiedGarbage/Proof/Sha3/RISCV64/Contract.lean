module

public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-3 on RISC-V: the contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/Sha3/Contract.lean`, which
imply these, with the arguments where the psABI passes them. The
permutation keeps its working space in a frame of 608 bytes below the stack
pointer (`Impl.Sha3.RISCV64.frameBytes`).
-/

@[expose] public section

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut
[u64; 64])`: applies Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap each other,
nor the 608 bytes below the stack pointer (its frame), which do not wrap
around. The stack pointer is 16-byte aligned. The pointers are public; the
state is secret. -/
def permuteRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let scratch : Region := ⟨s.gpr .a1, 512⟩
    let stack : Region := ⟨s.sp - 608, 608⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    s.sp.toNat % 16 = 0 ∧ 608 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .a0) = keccakF (stateAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha3
