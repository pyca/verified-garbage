module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# SHA-512: the RISC-V contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). The contracts of the RISC-V implementations of the
compression function and the streaming interface, in terms of
`Spec/Sha512.lean`.

The return address is in `ra`, which the target's calling convention
requires to be preserved (`VG.RISCV64.abiPreserved`), not on the stack.
`update` and `finalize` keep their working space in a frame of 208 bytes
below the stack pointer, which must not overlap their buffers.
-/

@[expose] public section

namespace VG.Proof.Sha512

open Spec.Sha512

open RISCV64 in
/-- RISC-V contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 18])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (144 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 64⟩
    let blocks : Region := ⟨s.gpr .a1, 128 * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, 144⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .a0) =
      compressBlocks (stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- RISC-V contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv` is
the initial hash value of `<alg>` (`H0_384`, `H0_512`, `H0_512_224` or
`H0_512_256`): makes the streaming state at `state` represent the empty
message, hashed from `iv`.

The code may write `state` (192 bytes). The pointer is public. -/
def initRISCV64 (iv : HashValue) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 192⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr iv s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- RISC-V contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize)`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

The code may read `data` (`len` bytes) and read and write `state` (192
bytes). These may not overlap each other, nor the 208 bytes below the stack
pointer (its frame), which do not wrap around. The stack pointer is 16-byte
aligned. The pointers, `count` and `len` are public; the state and the data
are secret. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 192⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := ⟨s.sp - 208, 208⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- RISC-V contract for `vg_<alg>_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; D])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the first `D`
bytes (`D` at most 64) of the final hash value `H⁽ᴺ⁾` of `m` from `iv` to
`out`: the digest of SHA-512, SHA-384, SHA-512/256 or SHA-512/224 for `D` =
64, 48, 32 or 28.

The code may read and write `state` (192 bytes, whose contents on exit are
unspecified) and `out` (`D` bytes). These may not overlap each other, nor the
208 bytes below the stack pointer (its frame), which do not wrap around. The
stack pointer is 16-byte aligned. The pointers and `count` are public; the
state is secret. -/
def finalizeDRISCV64 (D : Nat) : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 192⟩
    let out : Region := ⟨s.gpr .a2, D⟩
    let stack : Region := ⟨s.sp - 208, 208⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
    s.gpr .a1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .a2) D = (finalHash iv m).take D
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha512
