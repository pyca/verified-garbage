module

public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# SM3: the RISC-V contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply them
(`Contract.Implies`). The return address is in `ra`, which the target's
calling convention requires to be preserved (`VG.RISCV64.abiPreserved`),
not on the stack. `update` and `finalize` keep their working space in a
frame of 144 bytes below the stack pointer, which must not overlap their
buffers.
-/

@[expose] public section

namespace VG.Proof.Sm3

open Spec.Sm3

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 10])`:
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

open _root_.VG.RISCV64 in
/-- RISC-V contract for `vg_sm3_init(state: *mut [u8; 96])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (96 bytes). The pointer is public. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize)`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (96
bytes). These may not overlap each other, nor the 144 bytes below the stack
pointer (its frame), which do not wrap around. The stack pointer is 16-byte
aligned. The pointers, `count` and `len` are public; the state and the data
are secret. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open _root_.VG.RISCV64 in
/-- RISC-V contract for
`vg_sm3_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32])`: if
the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SM3 digest of `m` to `out`.

The code may read and write `state` (96 bytes, whose contents on exit are
unspecified) and `out` (32 bytes). These may not overlap each other, nor the
144 bytes below the stack pointer (its frame), which do not wrap around.
The stack pointer is 16-byte aligned. The pointers and `count` are public;
the state is secret. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 96⟩
    let out : Region := ⟨s.gpr .a2, 32⟩
    let stack : Region := ⟨s.sp - 144, 144⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 144 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ m, Repr s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .a2) 32 = Spec.Sm3.hash m
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm3
