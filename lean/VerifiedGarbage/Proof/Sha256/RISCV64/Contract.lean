module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# SHA-256: the RISC-V contract

**Untrusted**: the contract the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply it
(`Contract.Implies`). The contract of the RISC-V compression function, in
terms of `Spec/Sha256.lean`.

The return address is in `ra`, which the target's calling convention
requires to be preserved (`VG.RISCV64.abiPreserved`), not on the stack, so
no region needs to be kept disjoint from it.
-/

@[expose] public section

namespace VG.Proof.Sha256

open Spec.Sha256

open RISCV64 in
/-- RISC-V contract for
`vg_sha256_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 10])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(32 bytes) and `scratch` (80 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 32⟩
    let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 80⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .a0) =
      compressBlocks (stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha256
