module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# HMAC over any streaming hash function on PPC64LE: the contracts

Untrusted: the contracts the proofs are written against.

* `initK`, `updK` and `finK` are the PPC64LE contracts of a hash function's
  streaming `init`, `update` and `finalize` (with their working space as an
  argument), with the sizes and the representation of the streaming state
  as parameters. Each lets the callee use the 48 bytes below the stack
  pointer (a frame saving the link register), as SHA-256's, SHA-1's and
  MD5's do; the contracts the functions are proved against imply them (the
  SHA-512 family's, which use no stack, too).
* `initG`, `finG` and `longG` are those of HMAC's `init`, `finalize` and
  `initLong` with their working space as an argument, which push a frame of
  their own and let the functions they call use the 48 (`initLong`: 96)
  bytes below it; the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean`, which these imply.

The arguments are in `r3`–`r7` (ELFv2), and the return address is in the
link register, not on the stack, so no region needs to be kept disjoint from
it.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE

open VG.PPC64LE
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, S⟩
    s.rd = [] ∧ s.wr = [state] ∧ 48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint state
  post s s' := R s'.mem (s.gpr .r3) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, S⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, Wb⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint state ∧ (below s.sp 48).Disjoint data ∧
    (below s.sp 48).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .r3) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .r3) (m ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- `finalize(state, count, out, scratch)`, writing the `D`-byte digest
`hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, S⟩
    let out : Region := ⟨s.gpr .r5, D⟩
    let scratch : Region := ⟨s.gpr .r6, Wb⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint state ∧ (below s.sp 48).Disjoint out ∧
    (below s.sp 48).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .r3) m → m.length < 2 ^ 64 →
    s.gpr .r4 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .r5) D = hash m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-! ## Our functions

`SH` is a streaming hash function, `Wi` the bytes of scratch space and `F`
the bytes of stack below the stack pointer the code and its callees use. -/

variable (SH : StreamingHash) (Wi F : Nat)

/-- `init(inner, outer, key, key_len, scratch)`, for a key of at most a
block. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .r3, SH.stateBytes⟩
    let outer : Region := ⟨s.gpr .r4, SH.stateBytes⟩
    let key : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, Wi⟩
    (s.gpr .r6).toNat ≤ SH.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint inner ∧ (below s.sp F).Disjoint outer ∧ (below s.sp F).Disjoint key ∧
    (below s.sp F).Disjoint scratch
  post s s' :=
    let k0 := blockKey SH.H (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    SH.Repr s'.mem (s.gpr .r3) (xorPad k0 ipad) ∧ SH.Repr s'.mem (s.gpr .r4) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- `initLong(inner, outer, key, key_len, scratch)`, for a key longer than a
block: `initG`'s postcondition. -/
def longG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .r3, SH.stateBytes⟩
    let outer : Region := ⟨s.gpr .r4, SH.stateBytes⟩
    let key : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, Wi⟩
    SH.H.blockSize < (s.gpr .r6).toNat ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint inner ∧ (below s.sp F).Disjoint outer ∧ (below s.sp F).Disjoint key ∧
    (below s.sp F).Disjoint scratch
  post := (initG SH Wi F).post
  pub := (initG SH Wi F).pub

/-- `finalize(inner, outer, count, out, scratch)`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .r3, SH.stateBytes⟩
    let outer : Region := ⟨s.gpr .r4, SH.stateBytes⟩
    let out : Region := ⟨s.gpr .r6, SH.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r7, Wi⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    F ≤ s.sp.toNat ∧ (below s.sp F).Disjoint inner ∧ (below s.sp F).Disjoint outer ∧ (below s.sp F).Disjoint out ∧
    (below s.sp F).Disjoint scratch
  post s s' := ∀ k0 text, k0.length = SH.H.blockSize → k0.length + text.length < 2 ^ 64 →
    SH.Repr s.mem (s.gpr .r3) (xorPad k0 ipad ++ text) →
    s.gpr .r5 = BitVec.ofNat 64 (SH.H.blockSize + text.length) →
    SH.Repr s.mem (s.gpr .r4) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .r6) SH.digestBytes = hmacBlockKey SH.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac.Stream.PPC64LE
