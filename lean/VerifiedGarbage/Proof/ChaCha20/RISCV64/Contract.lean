module

public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ChaCha20: the RISC-V contract of the block function

**Untrusted**: the contract the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply it
(`Contract.Implies`). The contract of the assembly primitive
`vg_chacha20_block` on RISC-V, in terms of the specification in
`Spec/ChaCha20.lean`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open RISCV64 in
/-- RISC-V contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`:
writes `block` of the state at `state` to the first 16 words of `buf`.

The code may read `state` (64 bytes) and read and write `buf` (256 bytes;
its first 64 bytes hold the result on exit, and the rest is unspecified).
`buf` may not overlap `state`, and both are 4-byte aligned, as every caller's
are. The pointers are public; the state (key, counter and nonce) is secret. -/
def blockRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 64⟩
    let buf : Region := ⟨s.gpr .a1, 256⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧
      (s.gpr .a0).toNat % 4 = 0 ∧ (s.gpr .a1).toNat % 4 = 0
  post s s' := stateAt s'.mem (s.gpr .a1) = block (stateAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20
