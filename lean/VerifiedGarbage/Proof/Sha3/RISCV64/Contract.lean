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
pointer (`Impl.Sha3.RISCV64.frameBytes`); the streaming functions keep the
permutation's scratch space and the registers they save in a frame of their
own above it (`Impl.Sha3.RISCV64.Stream.frameBytes`, `padBytes`).
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

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_absorb(state = a0, rate = a1, pos = a2,
data = a3, len = a4) -> a0`: absorbs `data` into the streaming state
(`Repr`) and returns the new position in the block.

The code may read `data`, and read and write `state` (200 bytes), which do
not overlap each other or the 1168 bytes below the stack pointer (its frame
and the permutation's), which do not wrap around. The stack pointer is
16-byte aligned. `rate` is one of `rates`, and `pos < rate`. -/
def absorbRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat < (s.gpr .a1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .a0) (s.gpr .a1).toNat msg →
      (s.gpr .a2).toNat = msg.length % (s.gpr .a1).toNat →
      Repr s'.mem (s.gpr .a0) (s.gpr .a1).toNat
        (msg ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)) ∧
    (s'.gpr .a0).toNat = ((s.gpr .a2).toNat + (s.gpr .a4).toNat) % (s.gpr .a1).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_pad(state = a0, rate = a1, pos = a2,
suffix = a3)`: absorbs the padding (with the low byte of `suffix`) into the
streaming state.

The code may read and write `state` (200 bytes), which does not overlap the
1136 bytes below the stack pointer (its frame and the permutation's), which
do not wrap around. The stack pointer is 16-byte aligned. `rate` is one of
`rates`, and `pos < rate`. -/
def padRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let stack : Region := ⟨s.sp - 1136, 1136⟩
    s.rd = [] ∧ s.wr = [state] ∧
    s.sp.toNat % 16 = 0 ∧ 1136 ≤ s.sp.toNat ∧ stack.Disjoint state ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat < (s.gpr .a1).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .a0) (s.gpr .a1).toNat msg →
    (s.gpr .a2).toNat = msg.length % (s.gpr .a1).toNat →
    stateAt s'.mem (s.gpr .a0) =
      absorb (s.gpr .a1).toNat (pad (s.gpr .a1).toNat ((s.gpr .a3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_squeeze(state = a0, rate = a1, pos = a2,
out = a3, outlen = a4) -> a0`: writes `outlen` bytes of output from byte
`pos` on to `out`, and returns the position after them, leaving a state from
which the output continues.

The code may read and write `state` (200 bytes) and `out` (`outlen` bytes),
which do not overlap each other or the 1168 bytes below the stack pointer
(its frame and the permutation's), which do not wrap around. The stack
pointer is 16-byte aligned. `rate` is one of `rates`, and `pos ≤ rate`. -/
def squeezeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let out : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat ≤ (s.gpr .a1).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
      squeezeFrom (s.gpr .a1).toNat (stateAt s.mem (s.gpr .a0)) (s.gpr .a2).toNat (s.gpr .a4).toNat ∧
    (s'.gpr .a0).toNat ≤ (s.gpr .a1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .a1).toNat (stateAt s'.mem (s.gpr .a0)) (s'.gpr .a0).toNat d =
      squeezeFrom (s.gpr .a1).toNat (stateAt s.mem (s.gpr .a0))
        ((s.gpr .a2).toNat + (s.gpr .a4).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha3
