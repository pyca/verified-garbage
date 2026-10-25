module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# HMAC over any streaming hash function on RISC-V: the contracts

Untrusted: the contracts the proofs are written against.

* `initK`, `updK` and `finK` are the RISC-V contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters: `update` and
  `finalize` keep their working space in a frame of their own, in the `F`
  bytes below the stack pointer, as SHA-256's and SHA-512's do (with `F` =
  144 and 208), whose contracts are these.
* `initG` and `finG` are those of HMAC's `init` (for a key of any length)
  and `finalize`, which keep their working space in a frame of their own and
  let the functions they call use the stack below it: the `F` bytes below
  the stack pointer, all told. The artifacts are emitted with the shared
  contracts of `Spec/Hmac/Generic.lean`, which these imply.

The return address is in `ra`, which the target's calling convention
requires to be preserved (`VG.RISCV64.abiPreserved`), not on the stack.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64

open VG.RISCV64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, S⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := R s'.mem (s.gpr .a0) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

/-- `update(state, count, data, len)`, in a frame within the `F` bytes below
the stack pointer. -/
def updK (S F : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, S⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := below s.sp F
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data
  post s s' := ∀ m, R s.mem (s.gpr .a0) m → s.gpr .a1 = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .a0) (m ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `finalize(state, count, out)`, writing the `D`-byte digest `hash m`, for
a message of fewer than 2⁶⁴ bytes, in a frame within the `F` bytes below the
stack pointer. -/
def finK (S F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, S⟩
    let out : Region := ⟨s.gpr .a2, D⟩
    let stack : Region := below s.sp F
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out
  post s s' := ∀ m, R s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
    s.gpr .a1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .a2) D = hash m
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

/-! ## Our functions

`SH` is a streaming hash function and `F` the bytes of stack below the stack
pointer the code and its callees use. -/

variable (SH : StreamingHash) (F : Nat)

/-- `init(inner, outer, key, key_len)`, for a key of any length. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .a0, SH.stateBytes⟩
    let outer : Region := ⟨s.gpr .a1, SH.stateBytes⟩
    let key : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let stack : Region := below s.sp F
    s.rd = [key] ∧ s.wr = [inner, outer] ∧
    inner.Disjoint outer ∧ key.Disjoint inner ∧ key.Disjoint outer ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key
  post s s' :=
    let k0 := blockKey SH.H (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    SH.Repr s'.mem (s.gpr .a0) (xorPad k0 ipad) ∧ SH.Repr s'.mem (s.gpr .a1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- `finalize(inner, outer, count, out)`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .a0, SH.stateBytes⟩
    let outer : Region := ⟨s.gpr .a1, SH.stateBytes⟩
    let out : Region := ⟨s.gpr .a3, SH.digestBytes⟩
    let stack : Region := below s.sp F
    s.rd = [outer] ∧ s.wr = [inner, out] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ outer.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ F ≤ s.sp.toNat ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out
  post s s' := ∀ k0 text, k0.length = SH.H.blockSize → k0.length + text.length < 2 ^ 64 →
    SH.Repr s.mem (s.gpr .a0) (xorPad k0 ipad ++ text) →
    s.gpr .a2 = BitVec.ofNat 64 (SH.H.blockSize + text.length) →
    SH.Repr s.mem (s.gpr .a1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .a3) SH.digestBytes = hmacBlockKey SH.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac.Stream.RISCV64
