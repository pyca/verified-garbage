import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Impl.Pbkdf2.Stream.X86
import VerifiedGarbage.Proof.Framework.OmegaLit
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Md5.X86.Stream.Init
import VerifiedGarbage.Proof.Md5.X86.Stream.Md
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha1.X86.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86.Variants.Code
import VerifiedGarbage.Proof.Sha256.X86.Shared
import VerifiedGarbage.Proof.Sha256.X86.Variants.Code

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Contract`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the x86 contracts

The contracts the proofs are written against, as on the other targets
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`). Every argument is on the stack (cdecl).

* `initK`, `updK` and `finK` are the x86 contracts of a hash function's
  streaming `init`, `update` and `finalize` (`Proof.Sha512.initX86` and the
  others), with the sizes and the representation of the streaming state as
  parameters. `update` and `finalize` use the 20 bytes of stack below their
  return address. `finalize` may write its arguments, as MD5's and SHA-1's
  do (`Proof.Md5.finalizeX86`); one that only reads them (`finKr`, as
  SHA-512's) is verified against `finK` too (`finK_of_finKr`).
* `initG`, `finG` and `iterG` are those of our functions, which use 48
  bytes of stack (a frame of up to six arguments, a return address and the
  20 bytes `update` and `finalize` use), which no buffer overlaps; they may
  only read their arguments. `initW`, `finW` and `iterW` are the same with
  the arguments writable, as the shared contracts of
  `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean` (which the
  artifacts are emitted with, and which imply them: `Contract.Implies`) have
  them.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 64-bit `count` argument of `update` and `finalize`, in argument
slots 1 and 2 (cdecl: the low word first). -/
def count (s : State) : BitVec 64 := VG.X86.arg s 2 ++ VG.X86.arg s 1

/-- The 64-bit `count` argument of our `finalize`, in argument slots 2 and 3. -/
def countF (s : State) : BitVec 64 := VG.X86.arg s 3 ++ VG.X86.arg s 2

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (VG.X86.arg s 0).toNat + S ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := R s'.mem ((VG.X86.arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ VG.X86.arg s₁ 0 = VG.X86.arg s₂ 0

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, S⟩
    let data : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 5).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (VG.X86.arg s 0).toNat + S ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 5).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((VG.X86.arg s 0).setWidth 64) m → VG.Proof.Pbkdf2.Stream.X86.count s = BitVec.ofNat 64 m.length →
    R s'.mem ((VG.X86.arg s 0).setWidth 64) (m ++ bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. It may
write its arguments. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, S⟩
    let out : Region := ⟨(VG.X86.arg s 3).setWidth 64, F⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + F ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((VG.X86.arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    VG.Proof.Pbkdf2.Stream.X86.count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem ((VG.X86.arg s 3).setWidth 64) F).take D = hash m
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes: `finK`,
but only reading its arguments. -/
def finKr (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, S⟩
    let out : Region := ⟨(VG.X86.arg s 3).setWidth 64, F⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, Wb⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + F ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + Wb ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem ((VG.X86.arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    VG.Proof.Pbkdf2.Stream.X86.count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem ((VG.X86.arg s 3).setWidth 64) F).take D = hash m
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initScratchContract`,
reading its arguments only. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨(VG.X86.arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    (VG.X86.arg s 3).toNat ≤ S.H.blockSize ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
    S.Repr s'.mem ((VG.X86.arg s 0).setWidth 64) (xorPad k0 ipad) ∧
      S.Repr s'.mem ((VG.X86.arg s 1).setWidth 64) (xorPad k0 opad)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `finalize(inner, outer, count, out, scratch)`:
`VG.Spec.Hmac.finalizeScratchContract`, reading its arguments only. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨(VG.X86.arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.stateBytes⟩
    let out : Region := ⟨(VG.X86.arg s 4).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(VG.X86.arg s 5).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem ((VG.X86.arg s 0).setWidth 64) (xorPad k0 ipad ++ text) →
    VG.Proof.Pbkdf2.Stream.X86.countF s = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem ((VG.X86.arg s 1).setWidth 64) (xorPad k0 opad) →
    bytesAt s'.mem ((VG.X86.arg s 4).setWidth 64) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`,
reading its arguments only. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, 2 * S.stateBytes⟩
    let u : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.digestBytes⟩
    let t : Region := ⟨(VG.X86.arg s 3).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem ((VG.X86.arg s 0).setWidth 64) (xorPad k0 ipad) →
    S.Repr s.mem ((VG.X86.arg s 0).setWidth 64 + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem ((VG.X86.arg s 3).setWidth 64) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (VG.X86.arg s 2).toNat
        (bytesAt s.mem ((VG.X86.arg s 1).setWidth 64) S.digestBytes)
        (bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) S.digestBytes)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-! ## With the arguments writable -/

/-- `initG`, with the arguments writable, as `VG.Spec.Hmac.initScratchContract` has
them. -/
def initW : Contract isa where
  pre s :=
    let inner : Region := ⟨(VG.X86.arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    (VG.X86.arg s 3).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := (VG.Proof.Pbkdf2.Stream.X86.initG S W).post
  pub := (VG.Proof.Pbkdf2.Stream.X86.initG S W).pub

/-- `finG`, with the arguments writable, as `VG.Spec.Hmac.finalizeScratchContract`
has them. -/
def finW : Contract isa where
  pre s :=
    let inner : Region := ⟨(VG.X86.arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.stateBytes⟩
    let out : Region := ⟨(VG.X86.arg s 4).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(VG.X86.arg s 5).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post := (VG.Proof.Pbkdf2.Stream.X86.finG S W).post
  pub := (VG.Proof.Pbkdf2.Stream.X86.finG S W).pub

/-- `iterG`, with the arguments writable, as `VG.Spec.Pbkdf2.iterateContract`
has them. -/
def iterW : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, 2 * S.stateBytes⟩
    let u : Region := ⟨(VG.X86.arg s 1).setWidth 64, S.digestBytes⟩
    let t : Region := ⟨(VG.X86.arg s 3).setWidth 64, S.digestBytes⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch, args] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (VG.X86.arg s 3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (VG.X86.arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := (VG.Proof.Pbkdf2.Stream.X86.iterG S W).post
  pub := (VG.Proof.Pbkdf2.Stream.X86.iterG S W).pub

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash`. -/
section

/-!
# HMAC over any streaming hash function on x86 (32-bit): the functions we call

As on the other targets (`Proof/Pbkdf2/Stream/Arm/Hash.lean`): `HashOK H` is
what the proofs know of the hash function `H`: its streaming functions are
verified against `initK`, `updK` and `finK`, never write `esp` and use at most
20 bytes of stack, the representation of its streaming state is determined by
the state's bytes, and its sizes are small.

Each call is in a frame of its arguments (`WP.callWith`): `init_frame`,
`upd_frame` and `fin_frame` run one, from the state before its push, given
the registers pushed (`InitArgs`, `UpdArgs`, `FinArgs`, which give the
callee's precondition, `CallPre`). A call writes the 48 bytes below `esp`
(`stk`), which `After` lets change. `init_rel`, `upd_rel` and `fin_rel`
relate two runs of them (`RelCT.callWith`).
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Stream (Upd WP.cons)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's x86 functions, verified. `Wb` is the scratch
space their contracts use, at most the `8 W` bytes we give them. -/
structure HashOK (H : VG.Impl.Pbkdf2.Stream.X86.Hash) where
  SH : StreamingHash
  Wb : Nat
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  hDF : H.D ≤ H.F
  hF : H.F ≤ 64
  hD0 : 0 < H.D
  hS0 : 0 < H.S
  hSB : H.S ≤ 256
  hB0 : 0 < H.B
  hBB : H.B ≤ 128
  hWb : Wb ≤ 8 * H.W
  hW : H.W ≤ 64
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified X86.target H.initC (VG.Proof.Pbkdf2.Stream.X86.initK H.S SH.Repr)
  upd : Verified X86.target H.updC (VG.Proof.Pbkdf2.Stream.X86.updK H.S Wb SH.Repr)
  fin : Verified X86.target H.finC (VG.Proof.Pbkdf2.Stream.X86.finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initSp : NoSp H.initC
  updSp : NoSp H.updC
  finSp : NoSp H.finC
  initSU : stackUse H.initC ≤ 20
  updSU : stackUse H.updC ≤ 20
  finSU : stackUse H.finC ≤ 20

variable {H : VG.Impl.Pbkdf2.Stream.X86.Hash} (hH : VG.Proof.Pbkdf2.Stream.X86.HashOK H)

/-- The 48 bytes below `esp`, where our frames and calls go. -/
abbrev stk (s : State) : Region := below (s.gpr .esp) 48

/-- What a call leaves: the regions, the callee-saved registers (`esp`
among them), and memory outside what it may write and `stk`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (ws ++ [VG.Proof.Pbkdf2.Stream.X86.stk s]) s.mem s'.mem

theorem After.esp {s s' : State} {ws : List Region} (h : VG.Proof.Pbkdf2.Stream.X86.After s ws s') : s'.gpr .esp = s.gpr .esp :=
  h.cs .esp (by simp [calleeSaved])

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! ## The stack below `esp` -/

section Stack
variable {E : BitVec 32} (hE : 48 ≤ E.toNat)
include hE

/-- `n` bytes at `k ≥ n` below `E` are in `below E 48`. -/
theorem stk_sub {k n : Nat} (hn : n ≤ k) (hk : k ≤ 48) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64, n⟩ (below E 48) := by
  unfold below
  rw [Taint.sub_setWidth (by omega_nat), Taint.sub_setWidth (by omega_nat)]
  exact Offset.sub_below _ hk (by omega)

/-- The `n` bytes below `E - k`, as a contract writes them, are in `below E 48`. -/
theorem stk_sub' {k n : Nat} (h : k + n ≤ 48) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - BitVec.ofNat 64 n, n⟩ (below E 48) := by
  unfold below
  rw [Taint.sub_setWidth (by omega_nat), Taint.sub_setWidth (by omega_nat), Offset.sub_sub_ofNat]
  exact Offset.sub_below _ (by omega) (by omega)

end Stack

@[simp] theorem count_withRegions (s : State) (rd wr : List Region) :
    VG.Proof.Pbkdf2.Stream.X86.count (s.withRegions rd wr) = VG.Proof.Pbkdf2.Stream.X86.count s := rfl

theorem toNat_sub_ofNat {E : BitVec 32} {k : Nat} (h : k ≤ E.toNat) :
    (E - BitVec.ofNat 32 k).toNat = E.toNat - k := sub_toNat h

theorem zero_append_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have z : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, z, Nat.zero_shiftLeft, Nat.zero_or]
  omega_nat

/-- After a framed call, from what `WP.callWith` gives. -/
theorem after_of {s s' : State} {ws : List Region} {n : Nat} (h48 : 48 ≤ (s.gpr .esp).toNat) (hn : n ≤ 48)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (ws ++ [below (s.gpr .esp) n]) s.mem s'.mem) : VG.Proof.Pbkdf2.Stream.X86.After s ws s' :=
  ⟨hrd, hwr, hcs, Frame.below_mono hf hn h48⟩

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

/-! ## `init`, in a frame of its argument -/

/-- What a framed call of `init` on the state at `st` (in `r`) needs. -/
structure InitArgs (s : State) (r : Reg) (st : BitVec 32) : Prop where
  hst : s.gpr r = st
  hr : r ≠ .esp
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cw : Covers [⟨st.setWidth 64, H.S⟩] s.wr
  b_st : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  nst : st.toNat + H.S ≤ 2 ^ 32

/-- The regions `init` is given: its argument and the state. -/
abbrev InitArgs.rd (sp : BitVec 32) : List Region := [below sp 4]
abbrev InitArgs.wr (st : BitVec 32) : List Region := [⟨st.setWidth 64, H.S⟩]

namespace InitArgs
variable {s : State} {r : Reg} {st : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H) s r st)
include h

theorem fit : 4 * [r].length + 4 ≤ (s.gpr .esp).toNat := by have := h.sp48; simp only [List.length_cons, List.length_nil]; omega_nat
theorem nesp : Reg.esp ∉ [r] := by simp [Ne.symm h.hr]

theorem a0 : VG.X86.arg (pushed [r] s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst

theorem callPre : CallPre (VG.Proof.Pbkdf2.Stream.X86.initK H.S hH.SH.Repr) [r] (InitArgs.rd (s.gpr .esp)) (InitArgs.wr (H := H) st) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Pbkdf2.Stream.X86.initK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, callEntry_argAddr0, callEntry_esp', List.length_cons, List.length_nil]
    refine ⟨trivial, trivial, h.b_st.sub_left (below_sub (by omega_nat) e), ?_, h.nst, ?_⟩
    · exact h.b_st.sub_left (VG.Proof.Pbkdf2.Stream.X86.stk_sub e (by omega_nat) (by omega_nat))
    · rw [sub_toNat (by omega_nat)]; have := (s.gpr .esp).isLt; omega_nat
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact InRegions_append_cons.mpr (.inl hc)
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n hi
    obtain ⟨q', hq', hc'⟩ := h.cw a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

end InitArgs

theorem init_frame {s : State} {r : Reg} {st : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H) s r st) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.X86.After s [⟨st.setWidth 64, H.S⟩] s' → hH.SH.Repr s'.mem (st.setWidth 64) [] → Q s') :
    WP isa (H.callInit r) s Q := by
  have e := h.sp48
  have su := hH.initSU
  refine WP.callWith hH.init.1 hH.initSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega_nat) (h.callPre hH) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  refine hQ s' (VG.Proof.Pbkdf2.Stream.X86.after_of e (by simp only [List.length_cons, List.length_nil]; omega_nat) rd' wr' cs' f') ?_
  simp only [VG.Proof.Pbkdf2.Stream.X86.initK, arg_withRegions, h.a0] at post
  rw [← m₂]; exact post

/-! ## `update`, in a frame of its arguments -/

/-- What a framed call of `update` needs of the state before its push: the
state at `st` in `r`, the scratch space at `sc` in `ebp`, the `len` bytes of
data at `d` in `edx` and `ecx`, and the count, `0` in `eax` and `c` in
`lo`; the regions the callee may read and write; that they are disjoint as
it needs, and from the 48 bytes below `esp`; and that none of them wraps
around. -/
structure UpdArgs (s : State) (lo r : Reg) (st d sc c : BitVec 32) (len : Nat) : Prop where
  hst : s.gpr r = st
  hlo : s.gpr lo = c
  eax : s.gpr .eax = 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 len
  edx : s.gpr .edx = d
  ebp : s.gpr .ebp = sc
  hr : r ≠ .esp
  hl : lo ≠ .esp
  hlen : len < 2 ^ 32
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨sc.setWidth 64, hH.Wb⟩
  d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ ⟨st.setWidth 64, H.S⟩
  d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ ⟨sc.setWidth 64, hH.Wb⟩
  b_st : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  b_d : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨d.setWidth 64, len⟩
  b_sc : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨sc.setWidth 64, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  nd : d.toNat + len ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The six words `update`'s frame pushes, last to first. -/
abbrev upd6 (lo r : Reg) : List Reg := [.ebp, .ecx, .edx, .eax, lo, r]

/-- The regions `update` is given: the data and its arguments, the state and the scratch space. -/
abbrev UpdArgs.rd (sp d : BitVec 32) (len : Nat) : List Region :=
  [⟨d.setWidth 64, len⟩, below sp 24]
abbrev UpdArgs.wr (st sc : BitVec 32) : List Region := [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩]

namespace UpdArgs
variable {hH} {s : State} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
  (h : VG.Proof.Pbkdf2.Stream.X86.UpdArgs hH s lo r st d sc c len)
include h

theorem fit : 4 * (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r).length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega_nat
theorem nesp : Reg.esp ∉ VG.Proof.Pbkdf2.Stream.X86.upd6 lo r := by simp [Ne.symm h.hr, Ne.symm h.hl]

theorem a0 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst
theorem a1 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 1 = c := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hlo
theorem a2 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 2 = 0 := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.eax
theorem a3 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 3 = d := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.edx
theorem a4 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 4 = BitVec.ofNat 32 len := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ecx
theorem a5 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry 5 = sc := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ebp

theorem count_eq : VG.Proof.Pbkdf2.Stream.X86.count (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry = (0 : BitVec 32) ++ c := by
  rw [VG.Proof.Pbkdf2.Stream.X86.count, h.a1, h.a2]

theorem hlen' : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega_nat

theorem callPre : CallPre (VG.Proof.Pbkdf2.Stream.X86.updK H.S hH.Wb hH.SH.Repr) (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) (UpdArgs.rd (s.gpr .esp) d len) (UpdArgs.wr hH st sc) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Pbkdf2.Stream.X86.updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a3, h.a4, h.a5, h.hlen', callEntry_argAddr0, callEntry_esp', VG.Proof.Pbkdf2.Stream.X86.upd6,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6)).setWidth 64, 24⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub e (by omega_nat) (by omega_nat)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6 + 4)).setWidth 64, 4⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub e (by omega_nat) (by omega_nat)
    have sK : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 6 + 4)).setWidth 64 - 20, 20⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub' (n := 20) e (by omega_nat)
    refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, h.b_st.sub_left sA, h.b_sc.sub_left sA,
      h.b_st.sub_left sR, h.b_sc.sub_left sR, h.b_st.sub_left sK, h.b_sc.sub_left sK, h.b_d.sub_left sK,
      h.nst, h.nd, h.nsc, ?_, ?_⟩
    · rw [sub_toNat (by omega_nat)]; omega_nat
    · rw [sub_toNat (by omega_nat)]; have := (s.gpr .esp).isLt; omega_nat
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := h.cd a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n hi
    obtain ⟨q', hq', hc'⟩ := h.cw a n hi
    exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

/-- The callee's memory on entry is ours outside `stk`. -/
theorem entry_frame : Frame [VG.Proof.Pbkdf2.Stream.X86.stk s] s.mem (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry.mem :=
  (callEntry_frame h.fit h.nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega_nat) h.sp48⟩

end UpdArgs

theorem upd_frame {s : State} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
    (h : VG.Proof.Pbkdf2.Stream.X86.UpdArgs hH s lo r st d sc c len) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.X86.After s [⟨st.setWidth 64, H.S⟩, ⟨sc.setWidth 64, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (st.setWidth 64) m → (0 : BitVec 32) ++ c = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (st.setWidth 64) (m ++ bytesAt s.mem (d.setWidth 64) len)) → Q s') :
    WP isa (.frame (.push (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r)) (.call H.updN H.updC) (.pop .eax (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r).length)) s Q := by
  have e := h.sp48
  have su := hH.updSU
  refine WP.callWith hH.upd.1 hH.updSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega_nat) h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  refine hQ s' (VG.Proof.Pbkdf2.Stream.X86.after_of e (by simp only [List.length_cons, List.length_nil]; omega_nat) rd' wr' cs' f') fun m hr hc => ?_
  simp only [VG.Proof.Pbkdf2.Stream.X86.updK, arg_withRegions, State.withRegions_mem, h.a0, h.a3, h.a4, h.hlen'] at post
  have fE := h.entry_frame
  have hs : ∀ q ∈ [VG.Proof.Pbkdf2.Stream.X86.stk s], (⟨st.setWidth 64, H.S⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry.mem (st.setWidth 64) m :=
    hH.repr _ _ _ _ _ (fun i hi => fE.bytes (R := ⟨st.setWidth 64, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr
  have hd : bytesAt (pushed (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r) s).callEntry.mem (d.setWidth 64) len = bytesAt s.mem (d.setWidth 64) len := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact fE.bytes (R := ⟨d.setWidth 64, len⟩)
      (by simp only [List.mem_singleton]; rintro q rfl; exact h.b_d.symm) (by show len ≤ 2 ^ 64; have := h.hlen; omega_nat)
      (List.mem_range.mp hi)
  rw [← m₂, ← hd]
  exact post m hr' (by rw [VG.Proof.Pbkdf2.Stream.X86.count_withRegions, h.count_eq]; exact hc)

/-! ## `finalize`, in a frame of its arguments -/

/-- What a framed call of `finalize` needs of the state before its push:
the state at `st` in `r`, the count `hi ++ lo` in `ecx` and `eax`, and `out`
at `o` and the scratch space at `sc` in `edx` and `ebp`, as for `update`. -/
structure FinArgs (s : State) (r : Reg) (st o sc lo hi : BitVec 32) : Prop where
  hst : s.gpr r = st
  eax : s.gpr .eax = lo
  ecx : s.gpr .ecx = hi
  edx : s.gpr .edx = o
  ebp : s.gpr .ebp = sc
  hr : r ≠ .esp
  sp48 : 48 ≤ (s.gpr .esp).toNat
  cw : Covers [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨o.setWidth 64, H.F⟩
  st_sc : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨sc.setWidth 64, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o.setWidth 64, H.F⟩ ⟨sc.setWidth 64, hH.Wb⟩
  b_st : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  b_o : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨o.setWidth 64, H.F⟩
  b_sc : (VG.Proof.Pbkdf2.Stream.X86.stk s).Disjoint ⟨sc.setWidth 64, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  no : o.toNat + H.F ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The five words `finalize`'s frame pushes, last to first. -/
abbrev fin5 (r : Reg) : List Reg := [.ebp, .edx, .ecx, .eax, r]

/-- The regions `finalize` is given, all writable: the state, `out`, the
scratch space and its arguments. -/
abbrev FinArgs.wr (st o sc sp : BitVec 32) : List Region :=
  [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩, below sp 20]

namespace FinArgs
variable {hH} {s : State} {r : Reg} {st o sc lo hi : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.X86.FinArgs hH s r st o sc lo hi)
include h

theorem fit : 4 * (VG.Proof.Pbkdf2.Stream.X86.fin5 r).length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.sp48; simp only [List.length_cons, List.length_nil]; omega_nat
theorem nesp : Reg.esp ∉ VG.Proof.Pbkdf2.Stream.X86.fin5 r := by simp [Ne.symm h.hr]

theorem a0 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry 0 = st := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.hst
theorem a1 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry 1 = lo := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.eax
theorem a2 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry 2 = hi := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ecx
theorem a3 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry 3 = o := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.edx
theorem a4 : VG.X86.arg (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry 4 = sc := by
  rw [callEntry_arg h.fit h.nesp (by simp)]; simpa using h.ebp

theorem count_eq : VG.Proof.Pbkdf2.Stream.X86.count (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry = hi ++ lo := by
  rw [VG.Proof.Pbkdf2.Stream.X86.count, h.a1, h.a2]

theorem callPre : CallPre (VG.Proof.Pbkdf2.Stream.X86.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) (VG.Proof.Pbkdf2.Stream.X86.fin5 r) []
    (FinArgs.wr hH st o sc (s.gpr .esp)) s := by
  have e := h.sp48
  have fit := h.fit
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Pbkdf2.Stream.X86.finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, h.a0, h.a3, h.a4, callEntry_argAddr0, callEntry_esp', VG.Proof.Pbkdf2.Stream.X86.fin5,
      List.length_cons, List.length_nil]
    have sA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5)).setWidth 64, 20⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub e (by omega_nat) (by omega_nat)
    have sR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5 + 4)).setWidth 64, 4⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub e (by omega_nat) (by omega_nat)
    have sK : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 5 + 4)).setWidth 64 - 20, 20⟩ (VG.Proof.Pbkdf2.Stream.X86.stk s) :=
      VG.Proof.Pbkdf2.Stream.X86.stk_sub' (n := 20) e (by omega_nat)
    refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, h.b_st.sub_left sA, h.b_o.sub_left sA,
      h.b_sc.sub_left sA, h.b_st.sub_left sR, h.b_o.sub_left sR, h.b_sc.sub_left sR,
      h.b_st.sub_left sK, h.b_o.sub_left sK, h.b_sc.sub_left sK, h.nst, h.no, h.nsc, ?_, ?_⟩
    · rw [sub_toNat (by omega_nat)]; omega_nat
    · rw [sub_toNat (by omega_nat)]; have := (s.gpr .esp).isLt; omega_nat
  · intro a n ⟨q, hq, hc⟩
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_left 3
    · refine InRegions_append_cons.mpr (.inl ?_)
      simpa using hc
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    rotate_left 3
    · exact ⟨_, List.mem_cons_self, by simpa using hc⟩
    all_goals
      obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

theorem entry_frame : Frame [VG.Proof.Pbkdf2.Stream.X86.stk s] s.mem (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry.mem :=
  (callEntry_frame h.fit h.nesp).sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, below_sub (by simp only [List.length_cons, List.length_nil]; omega_nat) h.sp48⟩

end FinArgs

theorem fin_frame {s : State} {r : Reg} {st o sc lo hi : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.X86.FinArgs hH s r st o sc lo hi)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.X86.After s [⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (st.setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (o.setWidth 64) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push (VG.Proof.Pbkdf2.Stream.X86.fin5 r)) (.call H.finN H.finC) (.pop .eax (VG.Proof.Pbkdf2.Stream.X86.fin5 r).length)) s Q := by
  have e := h.sp48
  have su := hH.finSU
  refine WP.callWith hH.fin.1 hH.finSp (by simp) h.nesp
    (by simp only [List.length_cons, List.length_nil]; omega_nat) h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  have n5 : (VG.Proof.Pbkdf2.Stream.X86.fin5 r).length = 5 := rfl
  rw [n5] at f'
  have f'' : Frame ([⟨st.setWidth 64, H.S⟩, ⟨o.setWidth 64, H.F⟩, ⟨sc.setWidth 64, hH.Wb⟩] ++
      [below (s.gpr .esp) (4 * 5 + stackUse H.finC + 4)]) s.mem s'.mem :=
    Frame.sub f' fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          below_sub (by omega_nat) (by omega_nat)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          fun _ h => h⟩
  refine hQ s' (VG.Proof.Pbkdf2.Stream.X86.after_of e (by omega_nat) rd' wr' cs' f'')
    fun m hr hl hc => ?_
  simp only [VG.Proof.Pbkdf2.Stream.X86.finK, arg_withRegions, State.withRegions_mem, h.a0, h.a3] at post
  have fE := h.entry_frame
  have hs : ∀ q ∈ [VG.Proof.Pbkdf2.Stream.X86.stk s], (⟨st.setWidth 64, H.S⟩ : Region).Disjoint q := by
    simp only [List.mem_singleton]; rintro q rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed (VG.Proof.Pbkdf2.Stream.X86.fin5 r) s).callEntry.mem (st.setWidth 64) m :=
    hH.repr _ _ _ _ _ (fun i hi => fE.bytes (R := ⟨st.setWidth 64, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr
  rw [← m₂]
  exact post m hr' hl (by rw [VG.Proof.Pbkdf2.Stream.X86.count_withRegions, h.count_eq]; exact hc)

/-! ## The calls in two runs

A call in a frame of its arguments is constant time when the callee's
precondition holds in both runs, `esp` is the same in both, and so are the
registers pushed (`RelCT.callWith`). -/

include hH in
theorem init_rel {P : State → State → Prop} {sp : BitVec 32} {r : Reg} {st : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H) s r st ∧ VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H) s' r st ∧ s.gpr .esp = sp ∧
      s'.gpr .esp = sp) :
    RelCT isa P (H.callInit r) fun _ _ => True := by
  refine RelCT.callWith hH.init.1 hH.init.2.1 (InitArgs.rd sp) (InitArgs.wr (H := H) st) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.callPre hH
  have c' := a'.callPre hH
  rw [e] at c; rw [e'] at c'
  refine ⟨c, c', e.trans e'.symm, ?_, ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions, a.a0, a'.a0]

theorem upd_rel {P : State → State → Prop} {sp : BitVec 32} {lo r : Reg} {st d sc c : BitVec 32} {len : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Stream.X86.UpdArgs hH s lo r st d sc c len ∧ VG.Proof.Pbkdf2.Stream.X86.UpdArgs hH s' lo r st d sc c len ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r)) (.call H.updN H.updC) (.pop .eax (VG.Proof.Pbkdf2.Stream.X86.upd6 lo r).length))
      fun _ _ => True := by
  refine RelCT.callWith hH.upd.1 hH.upd.2.1 (UpdArgs.rd sp d len) (UpdArgs.wr hH st sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c₁ := a.callPre
  have c₂ := a'.callPre
  rw [e] at c₁; rw [e'] at c₂
  refine ⟨c₁, c₂, e.trans e'.symm, ?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions]
    rcases (by omega_nat : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a.a0, a'.a0]
    · rw [a.a1, a'.a1]
    · rw [a.a2, a'.a2]
    · rw [a.a3, a'.a3]
    · rw [a.a4, a'.a4]
    · rw [a.a5, a'.a5]

theorem fin_rel {P : State → State → Prop} {sp : BitVec 32} {r : Reg} {st o sc lo hi : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Stream.X86.FinArgs hH s r st o sc lo hi ∧ VG.Proof.Pbkdf2.Stream.X86.FinArgs hH s' r st o sc lo hi ∧
      s.gpr .esp = sp ∧ s'.gpr .esp = sp) :
    RelCT isa P (.frame (.push (VG.Proof.Pbkdf2.Stream.X86.fin5 r)) (.call H.finN H.finC) (.pop .eax (VG.Proof.Pbkdf2.Stream.X86.fin5 r).length))
      fun _ _ => True := by
  refine RelCT.callWith hH.fin.1 hH.fin.2.1 [] (FinArgs.wr hH st o sc sp) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c₁ := a.callPre
  have c₂ := a'.callPre
  rw [e] at c₁; rw [e'] at c₂
  refine ⟨c₁, c₂, e.trans e'.symm, ?_, fun i hi => ?_⟩
  · simp only [State.withRegions_gpr, callEntry_esp', e, e']
  · simp only [arg_withRegions]
    rcases (by omega_nat : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [a.a0, a'.a0]
    · rw [a.a1, a'.a1]
    · rw [a.a2, a'.a2]
    · rw [a.a3, a'.a3]
    · rw [a.a4, a'.a4]

/-! ## The pieces between the calls

The taint analysis checks the code between the calls from the registers
that hold our variables, and the words of the stack arguments (`argTaint`),
which the pieces read again: they are public, and the same in both runs as
long as nothing has written them (`ArgsKept`). -/

/-- The taint in which `esp`, the registers `rs` and the `n - 4` bytes of
stack arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := false, argLen := n }

/-- The `k` words of arguments of `s` are those of `s₀`. -/
def ArgsKept (s₀ : State) (k : Nat) (s : State) : Prop := ∀ i < k, VG.X86.arg s i = VG.X86.arg s₀ i

/-- The arguments lie outside the writable regions, and do not wrap around. -/
def ArgsOut (k : Nat) (s : State) : Prop :=
  (s.gpr .esp).toNat + (4 + 4 * k) ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4 + 4 * k⟩ r

theorem agree_argTaint {rs : List Reg} {k : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.gpr .esp = s₂.gpr .esp) (hw₁ : VG.Proof.Pbkdf2.Stream.X86.ArgsOut k s₁) (hw₂ : VG.Proof.Pbkdf2.Stream.X86.ArgsOut k s₂)
    (hm : ∀ i < k, VG.X86.arg s₁ i = VG.X86.arg s₂ i) : VG.X86.Taint.Agree (VG.Proof.Pbkdf2.Stream.X86.argTaint rs (4 + 4 * k)) s₁ s₂ := by
  have wf : ∀ s : State, VG.Proof.Pbkdf2.Stream.X86.ArgsOut k s → VG.X86.Taint.Wf (VG.Proof.Pbkdf2.Stream.X86.argTaint rs (4 + 4 * k)) s := fun s hs =>
    VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs.1, hs.2⟩, fun _ h => (List.not_mem_nil h).elim⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf s₁ hw₁, wf s₂ hw₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun j h4 hj => ?_⟩
  · simp only [VG.Proof.Pbkdf2.Stream.X86.argTaint, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hsp
    · exact h r hr
  · simp only [VG.Proof.Pbkdf2.Stream.X86.argTaint] at hj
    rw [show VG.X86.Taint.depth (VG.Proof.Pbkdf2.Stream.X86.argTaint rs (4 + 4 * k)).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hw₁.1 h4 hj, VG.X86.Taint.argByte_eq hw₂.1 h4 hj,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_nat)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_nat))]
    exact congrArg _ (hm _ (by omega_nat))

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.X86.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.X86.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common`. -/
section

/-!
# Calls of a streaming hash function on x86 (32-bit): byte loops, registers, stack

The byte loops, our caller's registers and the stack, which HMAC's `init` and
`finalize`, PBKDF2's `iterate` (`Proof/Pbkdf2/Md/X86/`) and the whole of
PBKDF2 (`Proof/Pbkdf2/Whole/X86/`) share.
-/

/-!
## The byte loops

As on the other targets
(`Proof/Pbkdf2/Stream/Arm/Common.lean`, whose byte-list lemmas from x86-64
are reused): the byte copy (`copy`) and the exclusive-or of `U` into `T`.
Each counts an index up from 0 and compares it with its bound. The model has no index registers,
so each access computes its address first: byte `k` of a buffer at
`p + o` is at `[x + o]` with `x = p + k`, which is `p + o + k`, as nothing
wraps around the 32-bit address space.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash copy at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd WP.cons wp_mov wp_movi wp_add wp_addi wp_cmp wp_cmpi wp_test
  wp_movzx8 wp_store8 sub_beq sub_ofNat eval_e eval_ne ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint xorBytes_snoc xorBytes_length'
  InRegions.right' add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xori {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xor {d r : Reg} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

/-- The zero flag of `test x, x`. -/
theorem test_z (x : BitVec 32) : (x &&& x == 0) = decide (x.toNat = 0) := by
  rw [BitVec.and_self]
  by_cases h : x.toNat = 0
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    simp [this]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; exact h (by rw [e]; rfl)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ b d) = addr (s.gpr b) d := rfl

theorem ofNat_succ32 (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

/-- Byte `k` of the buffer at `a + o`, as a loop addresses it. -/
theorem addr3 {a : BitVec 32} {k o : Nat} (h : a.toNat + o + k < 2 ^ 32) :
    addr (a + BitVec.ofNat 32 k) o = a.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega_nat), add_ofNat_add, Nat.add_comm]

/-- The flags after counting up to `k + 1 ≤ n`. -/
theorem count_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (k + 1) - BitVec.ofNat 32 n == 0) = decide (k + 1 = n) :=
  VG.Proof.Sha256.X86.Stream.sub_beq (by omega_nat) hn

/-- The registers the loops write. -/
abbrev clob : List Reg := [.eax, .ecx, .edx, .ebx]

/-- The registers `copy` writes. -/
abbrev cclob : List Reg := [.eax, .ecx, .edx]

theorem nm {r : Reg} {l : List Reg} (h : r ∉ l) (x : Reg) (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `ne` that runs its body `n > 0` times, each run
ending with the flags of `k + 1 = n`. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show VG.X86.eval .ne s' = _; rw [VG.Proof.Sha256.X86.Stream.eval_ne, hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-! ## `copy` -/

/-- After `k` bytes of a `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.X86.cclob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.X86.cclob, t.gpr r = s.gpr r
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ∉ VG.Proof.Pbkdf2.Stream.X86.cclob) (hd : dst ∉ VG.Proof.Pbkdf2.Stream.X86.cclob)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr src).setWidth 64 + BitVec.ofNat 64 so, n⟩
      ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      VG.Proof.Pbkdf2.Stream.X86.Copied s ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d)
        (bytesAt s.mem ((s.gpr src).setWidth 64 + BitVec.ofNat 64 so) n) t := by
  set A := (s.gpr src).setWidth 64 + BitVec.ofNat 64 so
  set B := (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d
  refine WP.seq (VG.Proof.Sha256.X86.Stream.wp_movi fun s₀ u₀ => WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Stream.X86.CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r hr => u₀.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .ecx), u₀.gpr,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Stream.X86.count_loop hn (VG.Proof.Pbkdf2.Stream.X86.CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_add fun t₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.other src hs, h.ecx, VG.Proof.Pbkdf2.Stream.X86.addr3 (by omega_nat)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_add fun t₅ u₅ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (VG.Proof.Pbkdf2.Stream.X86.nm hd .edx), u₂.other _ (VG.Proof.Pbkdf2.Stream.X86.nm hd .eax),
      u₁.other _ (VG.Proof.Pbkdf2.Stream.X86.nm hd .eax), h.other dst hd, h.ecx, VG.Proof.Pbkdf2.Stream.X86.addr3 (by omega_nat)])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₆ m₆ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_addi fun t₇ u₇ => VG.Proof.Sha256.X86.Stream.wp_cmpi fun t₈ f₈ _ z₈ => WP.block_nil ?_
  have h7 : t₇.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, VG.Proof.Pbkdf2.Stream.X86.ofNat_succ32]
  refine ⟨⟨by rw [f₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₈.gpr, u₇.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .ecx), m₆.gpr, u₅.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), u₄.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax),
        u₃.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .edx), u₂.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), u₁.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), h.other r hr],
    by rw [f₈.gpr, h7], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₅.gpr .edx).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.mem]
      simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
      ext i hi; simp
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_nat)
    rw [hl] at e'
    rw [f₈.mem, u₇.mem, m₆.mem, show Reg8.dl.reg = .edx from rfl, v, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      h.mem, bytesAt_snoc', e']
  · rw [z₈, h7, VG.Proof.Pbkdf2.Stream.X86.count_z hk hn']

/-! ## The exclusive-or of `U` into `T` -/

theorem xor_byte32 (a b : Byte) : ((a.setWidth 32 ^^^ b.setWidth 32).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor, Bool.xor_comm]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.X86.clob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = VG.WriteBytes.writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `ebp + uo` and `T` at `esi`. -/
theorem xor_ok {uo n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (huw : (s.gpr .ebp).toNat + uo + n ≤ 2 ^ 32) (htw : (s.gpr .esi).toNat + n ≤ 2 ^ 32)
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo, n⟩ ⟨(s.gpr .esi).setWidth 64, n⟩) :
    WP isa (.seq (.block [.mov .ecx (.imm 0)])
      (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (VG.Impl.Pbkdf2.Stream.X86.at_ .eax uo),
        .mov .eax (.reg .esi), .alu .add .eax (.reg .ecx), .movzx8 .ebx (VG.Impl.Pbkdf2.Stream.X86.at_ .eax 0), .alu .xor .edx (.reg .ebx),
        .store8 (VG.Impl.Pbkdf2.Stream.X86.at_ .eax 0) .dl, .alu .add .ecx (.imm 1), .alu .cmp .ecx (.imm (BitVec.ofNat 32 n))]) .ne)) s
      fun t => VG.Proof.Pbkdf2.Stream.X86.XorInv s ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo) ((s.gpr .esi).setWidth 64) n t := by
  set U := (s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo
  set T := (s.gpr .esi).setWidth 64
  refine WP.seq (VG.Proof.Sha256.X86.Stream.wp_movi fun s₀ u₀ => WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Stream.X86.XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r hr => u₀.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .ecx), u₀.gpr,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil]⟩
  refine VG.Proof.Pbkdf2.Stream.X86.count_loop hn (VG.Proof.Pbkdf2.Stream.X86.XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [VG.WriteBytes.writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [VG.WriteBytes.writeBytes, hl', Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_nat), Nat.lt_irrefl, ↓reduceIte]
  have gb := h.other .ebp (by decide)
  have gs := h.other .esi (by decide)
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_add fun t₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movzx8 (a := U + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, VG.Proof.Pbkdf2.Stream.X86.addr3 (by omega_nat)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun t₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_add fun t₅ u₅ => ?_
  have a₅ : t₅.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .eax 0) = T + BitVec.ofNat 64 k := by
    rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, h.ecx,
      VG.Proof.Pbkdf2.Stream.X86.addr3 (by omega_nat)]
    exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _)
  refine VG.Proof.Sha256.X86.Stream.wp_movzx8 (a := T + BitVec.ofNat 64 k) a₅
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact InRegions.right' (houtT k hk)) fun t₆ u₆ => ?_
  refine VG.Proof.Pbkdf2.Stream.X86.wp_xor fun t₇ u₇ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (a := T + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₇.other _ (by decide), u₆.other _ (by decide)]; exact a₅)
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact houtT k hk) fun t₈ m₈ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_addi fun t₉ u₉ => VG.Proof.Sha256.X86.Stream.wp_cmpi fun t₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have h9 : t₉.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₉.gpr, m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.ecx,
      VG.Proof.Pbkdf2.Stream.X86.ofNat_succ32]
  refine ⟨⟨by rw [f₁₀.rd, u₉.rd, m₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₁₀.wr, u₉.wr, m₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₁₀.gpr, u₉.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .ecx), m₈.gpr, u₇.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .edx), u₆.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .ebx),
        u₅.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), u₄.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), u₃.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .edx), u₂.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax),
        u₁.other r (VG.Proof.Pbkdf2.Stream.X86.nm hr .eax), h.other r hr],
    by rw [f₁₀.gpr, h9], ?_⟩, ?_⟩
  · have hv : (t₇.gpr .edx).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
      rw [u₇.gpr, u₆.other .edx (by decide), u₆.gpr, u₅.other .edx (by decide),
        u₄.other .edx (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, VG.Proof.Pbkdf2.Stream.X86.xor_byte32, rU, rT]
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega_nat)
    rw [hl'] at e'
    rw [f₁₀.mem, u₉.mem, m₈.mem, show Reg8.dl.reg = .edx from rfl, hv, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem, h.mem, e', bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [z₁₀, h9, VG.Proof.Pbkdf2.Stream.X86.count_z hk hn']

end VG.Proof.Pbkdf2.Stream.X86

/-!
## Our caller's registers

As on the other targets
(`Proof/Pbkdf2/Stream/Arm/Common.lean`): the callee-saved registers we use
(`ebx`, `esi`, `edi`, `ebp`) are stored in `scratch` after the working
space of the functions we call (`Hash.saved`), with `scratch` in `eax`, and
loaded back at the end, with `scratch` copied from `ebp` into `eax` first.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store sub_offset)
open VG.Proof.Hmac.Generic.Common (InRegions.right' add_ofNat_add)

variable (H : VG.Impl.Pbkdf2.Stream.X86.Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.ebx, .esi, .edi, .ebp]

theorem callee_saved : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ VG.Proof.Pbkdf2.Stream.X86.savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨scr.setWidth 64 + BitVec.ofNat 64 (8 * H.W), 16⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (scr.setWidth 64 + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 16 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega_nat

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 16) :
    Region.Sub ⟨scr.setWidth 64 + BitVec.ofNat 64 d, 4⟩ (VG.Proof.Pbkdf2.Stream.X86.saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega_nat, ← add_ofNat_add]
  exact VG.Proof.Sha256.X86.Stream.sub_offset (by omega_nat) (by omega_nat)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Stream.X86.saveR H scr).Disjoint r) :
    VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.X86.saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.slot_sub H scr h₁ h₂)) (by decide)

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s₁ m)
    (he : ∀ r ∈ VG.Proof.Pbkdf2.Stream.X86.savedRegs, s₁.gpr r = s₀.gpr r) : VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

/-- The memory after storing `g r` at `B + d` for each `(r, d)` of `l`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => VG.Proof.Pbkdf2.Stream.X86.saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.Proof.Pbkdf2.Stream.X86.saveMem s.mem ((s.gpr .eax).setWidth 64) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.store (VG.Impl.Pbkdf2.Stream.X86.at_ .eax p.2) p.1) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2⟩ := hl p (by simp)
    refine VG.Proof.Sha256.X86.Stream.wp_store (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2)
      (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, addr_eq h1]) h2 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep B h (by omega_nat) (by omega_nat)) (by decide)

theorem saveMem_other (m : Mem) (B : Addr) (g : Reg → BitVec 32) {d : Nat} (hd : d < 2 ^ 32) :
    ∀ l : List (Reg × Nat), (∀ q ∈ l, q.2 < 2 ^ 32 ∧ (d + 4 ≤ q.2 ∨ q.2 + 4 ≤ d)) →
    (VG.Proof.Pbkdf2.Stream.X86.saveMem m B g l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | [], _ => rfl
  | q :: l, h => by
    rw [VG.Proof.Pbkdf2.Stream.X86.saveMem, VG.Proof.Pbkdf2.Stream.X86.saveMem_other _ B g hd l fun q' hq' => h q' (List.mem_cons_of_mem _ hq'),
      VG.Proof.Pbkdf2.Stream.X86.readW_writeW_save _ _ _ hd (h q (by simp)).1 (h q (by simp)).2]

theorem saveMem_read (B : Addr) (g : Reg → BitVec 32) :
    ∀ (m : Mem) (l : List (Reg × Nat)), l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    (∀ p ∈ l, p.2 < 2 ^ 32) → ∀ p ∈ l, (VG.Proof.Pbkdf2.Stream.X86.saveMem m B g l).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1
  | _, [], _, _, p, hp => by cases hp
  | m, q :: l, hpw, hb, p, hp => by
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [VG.Proof.Pbkdf2.Stream.X86.saveMem, VG.Proof.Pbkdf2.Stream.X86.saveMem_other _ _ _ (hb p (by simp)) l
        (fun q' hq' => ⟨hb q' (List.mem_cons_of_mem _ hq'), hpw.1 q' hq'⟩), Mem.readW_writeW_self32]
    · rw [VG.Proof.Pbkdf2.Stream.X86.saveMem]
      exact VG.Proof.Pbkdf2.Stream.X86.saveMem_read B g _ l hpw.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq')) p hp

theorem saveMem_frameR (B : Addr) (g : Reg → BitVec 32) (o L : Nat) (hL : o + L < 2 ^ 64) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, o ≤ p.2 ∧ p.2 + 4 ≤ o + L) →
    Frame [⟨B + BitVec.ofNat 64 o, L⟩] m (VG.Proof.Pbkdf2.Stream.X86.saveMem m B g l)
  | _, [], _ => Frame.refl _ _
  | m, p :: l, hl => by
    obtain ⟨h₁, h₂⟩ := hl p (by simp)
    have c : (⟨B + BitVec.ofNat 64 o, L⟩ : Region).Contains (B + BitVec.ofNat 64 p.2) (32 / 8) := by
      rw [show p.2 = o + (p.2 - o) by omega_nat, ← add_ofNat_add]
      exact VG.Proof.Sha256.X86.contains_offset (by omega_nat) (by omega_nat)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c).trans
      (VG.Proof.Pbkdf2.Stream.X86.saveMem_frameR B g o L hL _ l fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem save_eq : H.save = H.saved.map (fun p => Instr.store (VG.Impl.Pbkdf2.Stream.X86.at_ .eax p.2) p.1) := rfl

/-- Saving the registers, with `scratch` in `eax`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (hax : s.gpr .eax = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [VG.Proof.Pbkdf2.Stream.X86.saveR H scr] s.mem s'.mem → VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [VG.Proof.Pbkdf2.Stream.X86.save_eq]
  refine VG.Proof.Pbkdf2.Stream.X86.saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.X86.saved_mem H hp
    rw [hax]
    exact ⟨by omega_nat, ⟨_, hsc, VG.Proof.Sha256.X86.contains_offset (by omega_nat) (by omega_nat)⟩⟩
  · rw [m, hax]
    exact VG.Proof.Pbkdf2.Stream.X86.saveMem_frameR _ _ _ _ (by omega_nat) _ _ fun p hp => VG.Proof.Pbkdf2.Stream.X86.saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact VG.Proof.Pbkdf2.Stream.X86.saveMem_read _ _ _ _ (VG.Proof.Pbkdf2.Stream.X86.saved_pairwise H) (fun q hq => by have := VG.Proof.Pbkdf2.Stream.X86.saved_mem H hq; omega_nat) p hp

theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .eax ∧ (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.mov p.1 (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .eax p.2))) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine VG.Proof.Sha256.X86.Stream.wp_movm (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, addr_eq h2]) h3
      fun s₁ u₁ => ?_
    have eb : s₁.gpr .eax = s.gpr .eax := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq :
    H.restore = .mov .eax (.reg .ebp) :: H.saved.map (fun p => Instr.mov p.1 (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .eax p.2))) := rfl

theorem saved_fst : H.saved.map Prod.fst = VG.Proof.Pbkdf2.Stream.X86.savedRegs := rfl

/-- Loading them back, with `scratch` in `ebp`. -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (hbp : s.gpr .ebp = scr) {s₀ : State} (hs : VG.Proof.Pbkdf2.Stream.X86.SavedRegs H scr s₀ s.mem) (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ VG.Proof.Pbkdf2.Stream.X86.savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ VG.Proof.Pbkdf2.Stream.X86.savedRegs → r ≠ .eax → s'.gpr r = s.gpr r) := by
  rw [VG.Proof.Pbkdf2.Stream.X86.restore_eq]
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr := by rw [u₁.gpr, hbp]
  rw [← List.append_nil (List.map _ _)]
  refine VG.Proof.Pbkdf2.Stream.X86.restoreList_ok H.saved s₁ _ (by rw [VG.Proof.Pbkdf2.Stream.X86.saved_fst]; decide) (fun p hp => ?_)
    fun s₂ hl ho hm hrd hwr => WP.block_nil ⟨by rw [hm, u₁.mem], by rw [hrd, u₁.rd], by rw [hwr, u₁.wr],
      fun r hr => ?_, fun r hr hr' => ?_⟩
  · have := VG.Proof.Pbkdf2.Stream.X86.saved_mem H hp
    refine ⟨?_, by rw [e₁]; omega_nat, ?_⟩
    · simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    · rw [e₁, u₁.rd, u₁.wr]; exact InRegions.right' ⟨_, hsc, VG.Proof.Sha256.X86.contains_offset (by omega_nat) (by omega_nat)⟩
  · have hv : ∀ p ∈ H.saved, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      rw [hl p hp, e₁, u₁.mem, hs p hp]
    simp only [VG.Proof.Pbkdf2.Stream.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hv (.ebx, 8 * H.W) (by simp [Hash.saved])
    · exact hv (.esi, 8 * H.W + 4) (by simp [Hash.saved])
    · exact hv (.edi, 8 * H.W + 8) (by simp [Hash.saved])
    · exact hv (.ebp, 8 * H.W + 12) (by simp [Hash.saved])
  · rw [ho r (by rw [VG.Proof.Pbkdf2.Stream.X86.saved_fst]; exact hr), u₁.other r hr']

/-! ## Odds and ends -/

theorem toNat_setWidth (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_nat)

/-- `x + o`, as a register holds it, where nothing wraps around. -/
theorem setWidth_add {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := x) (k := o) h
  simpa only [addr] using this

theorem toNat_add_ofNat {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_nat), Nat.mod_eq_of_lt h]

/-! ## The stack

The 48 bytes below `esp` lie below the return address and the arguments;
what does not write those leaves them, and our arguments, as on entry. -/

theorem stk_ret {E : BitVec 32} (hE : 48 ≤ E.toNat) (_hf : E.toNat + 4 ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨E.setWidth 64, 4⟩ := by
  unfold below
  rw [Taint.sub_setWidth hE]
  exact Offset.below_disjoint _ (by omega_nat)

theorem stk_args {E : BitVec 32} {n : Nat} (hE : 48 ≤ E.toNat) (hf : E.toNat + 4 + n ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨addr E 4, n⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro a _ h₂; simp only [Region.Contains] at h₂; omega_nat
  unfold below
  rw [Taint.sub_setWidth hE, addr_eq (by omega_nat)]
  exact Offset.disjoint_below_above _ (by omega_nat)

/-- Argument `i` is at `4 i` bytes into the arguments. -/
theorem argAddr_eq (s : State) (i : Nat) :
    argAddr s i = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := rfl

/-- Where argument `i` is read, while `esp` is as on entry. -/
theorem argW {s₀ s : State} (hs : s.gpr .esp = s₀.gpr .esp) (i : Nat) :
    s.ea (VG.Impl.Pbkdf2.Stream.X86.at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, hs]; rfl

theorem arg_sub {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : Region.Sub ⟨argAddr s i, 4⟩ ⟨addr E 4, n⟩ := by
  rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hs, addr_eq (by omega_nat), show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
    addr E (4 + 4 * i) from rfl, addr_eq (by omega_nat)]
  exact Offset.sub _ (by omega_nat) (by omega_nat)

theorem arg_contains {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : (⟨addr E 4, n⟩ : Region).Contains (argAddr s i) 4 := by
  rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hs, addr_eq (by omega_nat), show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
    addr E (4 + 4 * i) from rfl, addr_eq (by omega_nat)]
  exact Offset.contains _ (by omega_nat) (by omega_nat) (by omega_nat)

/-- The arguments are kept by what writes elsewhere. -/
theorem arg_keep {E : BitVec 32} {s₀ s : State} (h₀ : s₀.gpr .esp = E) (hs : s.gpr .esp = E) {n : Nat}
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) {rs : List Region} (hm : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr E 4, n⟩ r) {i : Nat} (hi : 4 * i + 4 ≤ n) : VG.X86.arg s i = VG.X86.arg s₀ i := by
  simp only [VG.X86.arg]
  rw [show argAddr s i = argAddr s₀ i by rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hs, h₀]]
  exact hm.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub h₀ hi hf)) (by decide)

/-- A streaming state is kept by what writes elsewhere. -/
theorem repr_keep {H : VG.Impl.Pbkdf2.Stream.X86.Hash} (hH : VG.Proof.Pbkdf2.Stream.X86.HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Finalize`. -/
section

/-!
# HMAC on x86 (32-bit): the start of `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86.lean`) starts by finalizing the inner
state with the hash function's streaming `finalize`, called with the code of
`Impl/Pbkdf2/Stream/X86.lean`: the prologue (`pro_ok`) loads `scratch`,
`inner`, `outer` and `out` (after our caller's registers are saved in
`scratch`), and the count just before the call, which passes it on
(`fin1Args_ok`, `finCall_ok`). What the rest keeps is `KR`;
`Proof/Pbkdf2/Md/X86/HmacFin.lean` continues from there.
-/

namespace VG.Proof.Pbkdf2.Stream.X86.Finalize

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash copy at_)
open VG.Proof.Pbkdf2.Stream.X86
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 sub_of_off sub_of_self bytes_keep
  bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : VG.Impl.Pbkdf2.Stream.X86.Hash} (hH : VG.Proof.Pbkdf2.Stream.X86.HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := VG.X86.arg s₀ 0
abbrev outer : BitVec 32 := VG.X86.arg s₀ 1
abbrev op : BitVec 32 := VG.X86.arg s₀ 4
abbrev scr : BitVec 32 := VG.X86.arg s₀ 5
abbrev inR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64, H.S⟩
abbrev outerR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.outer s₀).setWidth 64, H.S⟩
abbrev opR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.op s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀) 4, 24⟩
abbrev retR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀) 48
/-- Where the digests go. -/
abbrev T : Addr := (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨(VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).setWidth 64, hH.Wb⟩
/-- `T`, as a register holds it. -/
abbrev tO : BitVec 32 := VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀ + BitVec.ofNat 32 H.buf

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Stream.X86.Finalize.outerR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.outerR (H := H) s₀)
  i_p : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀)
  i_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  o_p : (VG.Proof.Pbkdf2.Stream.X86.Finalize.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀)
  o_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  p_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  a_i : (VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀)
  a_p : (VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀)
  a_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  r_i : (VG.Proof.Pbkdf2.Stream.X86.Finalize.retR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀)
  r_p : (VG.Proof.Pbkdf2.Stream.X86.Finalize.retR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀)
  r_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.retR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  b_i : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀)
  b_o : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.outerR (H := H) s₀)
  b_p : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀)
  b_s : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀)
  ni : (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (VG.Proof.Pbkdf2.Stream.X86.Finalize.outer s₀).toNat + H.S ≤ 2 ^ 32
  np : (VG.Proof.Pbkdf2.Stream.X86.Finalize.op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀).toNat
  spf : (VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀).toNat + 28 ≤ 2 ^ 32
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (VG.Proof.Pbkdf2.Stream.X86.finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀ := by
    simp only [VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR, below]; rw [Taint.sub_setWidth h22]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, hfit, ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Hash.buf] at *
  exact VG.Proof.Sha256.X86.Stream.sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.Finalize.tR (H := H) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact VG.Proof.Sha256.X86.Stream.sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (VG.Proof.Pbkdf2.Stream.X86.Finalize.calR hH s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (VG.Proof.Pbkdf2.Stream.X86.Finalize.calR hH s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)) := by
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 16) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (VG.Proof.Pbkdf2.Stream.X86.Finalize.calR hH s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.tR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hD
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.tR (H := H) s₀) := by
  have := hp.hW; have := hp.hD
  exact off_disj _ (a := 8 * H.W) (m := 16) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

theorem addr_tO : (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀).setWidth 64 = VG.Proof.Pbkdf2.Stream.X86.Finalize.T (H := H) s₀ :=
  VG.Proof.Pbkdf2.Stream.X86.setWidth_add (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem toNat_tO : (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀).toNat = (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀).toNat + H.buf :=
  VG.Proof.Pbkdf2.Stream.X86.toNat_add_ofNat (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem stk_arg : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀) := VG.Proof.Pbkdf2.Stream.X86.stk_args hp.sp48 (by have := hp.spf; omega_nat)

theorem stk_ret' : (VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Stream.X86.Finalize.retR s₀) := VG.Proof.Pbkdf2.Stream.X86.stk_ret hp.sp48 (by have := hp.spf; omega_nat)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀
  ebp : s.gpr .ebp = VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀
  ebx : s.gpr .ebx = VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀
  edi : s.gpr .edi = VG.Proof.Pbkdf2.Stream.X86.Finalize.op s₀
  saved : VG.Proof.Pbkdf2.Stream.X86.SavedRegs H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) s₀ s.mem
  frame : Frame (VG.Proof.Pbkdf2.Stream.X86.Finalize.wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .edi]

theorem kregs_callee : ∀ r ∈ VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs, r ∈ calleeSaved := by decide
theorem kregs_clob : ∀ r ∈ VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs, r ≠ .esp → r ∉ VG.Proof.Pbkdf2.Stream.X86.cclob := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.Pbkdf2.Stream.X86.Finalize.wrs (H := H) sc s₀, Region.Sub r r') : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.edi, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) : VG.Proof.Pbkdf2.Stream.X86.stk s = VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀ := by rw [VG.Proof.Pbkdf2.Stream.X86.stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Stream.X86.Finalize.Pre (H := H) sc s₀)
include hp

theorem argR_in : VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.argR_in hp, VG.Proof.Pbkdf2.Stream.X86.arg_contains rfl (by omega_nat) (by have := hp.spf; omega_nat)⟩

theorem KR.argEq {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  VG.Proof.Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 24) (by have := hp.spf; omega_nat) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_p
    · exact hp.a_s
    · exact (VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_arg hp).symm) (by omega_nat)

theorem KR.readArg {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, VG.Proof.Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) :
    s.mem.readW ((VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.Pbkdf2.Stream.X86.Finalize.E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := VG.Proof.Pbkdf2.Stream.X86.Finalize.retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_p
    · exact hp.r_s
    · exact (VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_ret' hp).symm) (by decide)

theorem wr_mem : VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Stream.X86.Finalize.opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

/-- `KR` after a call that writes `rs`, parts of our buffers, and keeps `esi`. -/
theorem KR.call {s s' : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) {rs : List Region} (ha : VG.Proof.Pbkdf2.Stream.X86.After s rs s')
    (hs : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, Region.Sub r (VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) ∨ r = VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀) :
    VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (VG.Proof.Pbkdf2.Stream.X86.Finalize.kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · rcases hsub r hr with h | rfl
      · exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀, by simp, h⟩
      · exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀, by simp, fun _ h => h⟩

/-! ## The pieces -/

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s ∧ s.gpr .esi = VG.Proof.Pbkdf2.Stream.X86.Finalize.outer s₀ ∧
    Frame [VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)] s₀.mem s.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw; have hD := hp.hD
  simp only [Hash.buf] at hf
  obtain ⟨sR, _, _⟩ := VG.Proof.Pbkdf2.Stream.X86.Finalize.wr_mem hp
  have dA : ∀ r ∈ [VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)], (VG.Proof.Pbkdf2.Stream.X86.Finalize.argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)
  simp only [Hash.finPrologue, List.singleton_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 5) (VG.Proof.Pbkdf2.Stream.X86.argW rfl 5) (VG.Proof.Pbkdf2.Stream.X86.Finalize.argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.Pbkdf2.Stream.X86.save_ok H (scr := VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_nat) (by omega_nat)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [VG.Proof.Pbkdf2.Stream.X86.saveR H (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub rfl (by omega_nat) (by have := hp.spf; omega_nat))) (by decide)
  have i₂ : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.Stream.X86.Finalize.argIn hp rfl rfl hi
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 0) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 1) (by
      rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 4) (by
      rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 4 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)],
    by rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, rA 4 (by decide)],
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [VG.Proof.Pbkdf2.Stream.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀, by simp, VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp⟩⟩,
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)], hm ▸ f₂'⟩

/-- The arguments of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ t) {lo hi : BitVec 32} (hax : t.gpr .eax = lo)
    (hcx : t.gpr .ecx = hi) (hdx : t.gpr .edx = VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀) :
    VG.Proof.Pbkdf2.Stream.X86.FinArgs hH t .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) lo hi := by
  have hwb := hH.hWb; have hf := hp.fits; have hf' := hp.fits; have hD := hp.hD; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Stream.X86.Finalize.wr_mem hp
  exact
    { hst := hk.ebx, eax := hax, ecx := hcx, edx := hdx, ebp := hk.ebp, hr := by decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by
        rw [hk.wr, VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := VG.Proof.Pbkdf2.Stream.X86.Finalize.scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]; exact hp.i_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.t_sub hp)
      st_sc := hp.i_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_sub hH hp)
      o_sc := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]; exact (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_t hH hp).symm
      b_st := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk]; exact hp.b_i
      b_o := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk, VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.t_sub hp)
      b_sc := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk]; exact hp.b_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_sub hH hp)
      nst := hp.ni
      no := by rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.toNat_tO hp]; omega_nat
      nsc := by omega_nat }

/-- The first call's arguments: the count from the stack. -/
theorem fin1Args_ok {s : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s) :
    WP isa (.block ([] ++ Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.buf)) s fun t =>
      VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ t ∧ VG.Proof.Pbkdf2.Stream.X86.FinArgs hH t .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) (VG.X86.arg s₀ 2) (VG.X86.arg s₀ 3) ∧
        t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem := by
  simp only [Hash.count1, Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 2) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, hk.esp]; rfl) (VG.Proof.Pbkdf2.Stream.X86.Finalize.argIn hp hk.rd hk.wr (by decide))
    fun s₁ u₁ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ 3) (by rw [VG.Proof.Pbkdf2.Stream.X86.ea_at, u₁.other _ (by decide), hk.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Pbkdf2.Stream.X86.Finalize.argIn hp hk.rd hk.wr (by decide)) fun s₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₃ u₃ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₄ u₄ => WP.block_nil ?_
  have k₄ : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s₄ := (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄
  refine ⟨k₄, VG.Proof.Pbkdf2.Stream.X86.Finalize.finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.readArg hp (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hk.readArg hp (by decide)]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.ebp]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]

theorem finCall_ok {t : State} (hk : VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ t) {lo hi : BitVec 32}
    (ha : VG.Proof.Pbkdf2.Stream.X86.FinArgs hH t .ebx (VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.tO (H := H) s₀) (VG.Proof.Pbkdf2.Stream.X86.Finalize.scr s₀) lo hi) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.X86.Finalize.KR (H := H) sc s₀ s' → s'.gpr .esi = t.gpr .esi →
      Frame [VG.Proof.Pbkdf2.Stream.X86.Finalize.inR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.tR (H := H) s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.calR hH s₀, VG.Proof.Pbkdf2.Stream.X86.Finalize.stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem ((VG.Proof.Pbkdf2.Stream.X86.Finalize.inn s₀).setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (VG.Proof.Pbkdf2.Stream.X86.Finalize.T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push (VG.Proof.Pbkdf2.Stream.X86.fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (VG.Proof.Pbkdf2.Stream.X86.fin5 .ebx).length)) t Q :=
  VG.Proof.Pbkdf2.Stream.X86.fin_frame hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.stk_eq hk, VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp] at f
    rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp] at hpost
    refine hQ s' (hk.call hp ha' ?_ ?_) (ha'.cs .esi (by simp [calleeSaved])) f hpost
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Stream.X86.Finalize.save_sub hp)
      · exact VG.Proof.Pbkdf2.Stream.X86.Finalize.save_t hp
      · exact (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_save hH hp).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [VG.Proof.Pbkdf2.Stream.X86.Finalize.addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact .inr rfl
      · exact .inl (VG.Proof.Pbkdf2.Stream.X86.Finalize.t_sub hp)
      · exact .inl (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_sub hH hp)

end

end VG.Proof.Pbkdf2.Stream.X86.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes`. -/
section

/-!
# HMAC over any streaming hash function on x86 (32-bit): the hash functions

`HashOK` for MD5 and the SHA-512 family, from their own proofs, as on
the other targets (`Proof/Pbkdf2/Stream/Arm/Hashes.lean`). Their contracts are
`initK`, `updK` and `finK` at their sizes, but for the SHA-512 family's
`update` and `finalize`, which hold from any initial hash value, and whose
`finalize` only reads its arguments (`finKr`). Another hash function with
streaming functions verified on x86 is one more `HashOK` here, and a
registration file for each of its functions. SHA-256's and SHA-1's, for
each of their backends, are in `Sha256.lean` and `Sha1.lean`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Hmac.Generic.Common (md5_repr sha512_repr finalHash_length)

/-- No instruction of `c` writes `esp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) : NoSp c :=
  NoSp.of_all h

/-- A `finalize` that only reads its arguments is verified against `finK`,
which lets it write them. -/
theorem finK_of_finKr {c : Prog isa} {S Wb F D : Nat} {R : Mem → Addr → List Byte → Prop}
    {hash : List Byte → List Byte} (h : Verified X86.target c (VG.Proof.Pbkdf2.Stream.X86.finKr S Wb F D R hash)) :
    Verified X86.target c (VG.Proof.Pbkdf2.Stream.X86.finK S Wb F D R hash) := by
  have pre : ∀ s, (VG.Proof.Pbkdf2.Stream.X86.finK S Wb F D R hash).pre s → (VG.Proof.Pbkdf2.Stream.X86.finKr S Wb F D R hash).pre (s.withRegions
      [⟨argAddr s 0, 20⟩] [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 3).setWidth 64, F⟩, ⟨(arg s 4).setWidth 64, Wb⟩]) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    simp only [VG.Proof.Pbkdf2.Stream.X86.finKr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  have pre' : ∀ s, (VG.Proof.Pbkdf2.Stream.X86.finKr S Wb F D R hash).pre s → (VG.Proof.Pbkdf2.Stream.X86.finK S Wb F D R hash).pre (s.withRegions []
      [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 3).setWidth 64, F⟩, ⟨(arg s 4).setWidth 64, Wb⟩, ⟨argAddr s 0, 20⟩]) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    simp only [VG.Proof.Pbkdf2.Stream.X86.finK, arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine Verified.narrowTo h _ _ pre (fun s h => ?_) (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (h.2.2.elim fun s hs => ⟨_, pre' s hs⟩)
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

/-! ## MD5 -/

def md5H : VG.Impl.Pbkdf2.Stream.X86.Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.X86.Stream.init,
  "vg_md5_update_scratch", Impl.Md5.X86.Stream.update, "vg_md5_finalize_scratch", Impl.Md5.X86.Stream.finalize⟩

def md5OK : VG.Proof.Pbkdf2.Stream.X86.HashOK VG.Proof.Pbkdf2.Stream.X86.md5H := by
  refine {
    SH := Spec.Hmac.md5S
    Wb := 112
    hS := rfl
    hD := rfl
    hB := rfl
    hDF := by decide
    hF := by decide
    hD0 := by decide
    hS0 := by decide
    hSB := by decide
    hB0 := by decide
    hBB := by decide
    hWb := by decide
    hW := by decide
    repr := md5_repr
    init := Proof.Md5.X86.Stream.init_verified
    upd := Proof.Md5.X86.Stream.Update.update_verified
    fin := Proof.Md5.X86.Stream.Finalize.finalize_verified.of_implies
      { pre := fun _ h => h
        post := fun s s' _ h m hr _ hc => by
          show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
          rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
          exact h m hr hc
        pub := fun _ _ _ _ h => h
        sat := Proof.Md5.X86.Stream.Finalize.finalize_verified.2.2 }
    initSp := VG.Proof.Pbkdf2.Stream.X86.nosp_of ?_
    updSp := VG.Proof.Pbkdf2.Stream.X86.nosp_of ?_
    finSp := VG.Proof.Pbkdf2.Stream.X86.nosp_of ?_
    initSU := ?_
    updSU := ?_
    finSU := ?_ }
  taint_decide_all

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : VG.Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.X86.Stream.init iv, "vg_sha512_update_scratch",
    Impl.Sha512.X86.Stream.update, "vg_sha512_finalize_scratch", Impl.Sha512.X86.Stream.finalize⟩

theorem sha512_updSp : NoSp Impl.Sha512.X86.Stream.update := VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)
theorem sha512_finSp : NoSp Impl.Sha512.X86.Stream.finalize := VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)
theorem sha512_updSU : stackUse Impl.Sha512.X86.Stream.update = 20 := by lit_decide
theorem sha512_finSU : stackUse Impl.Sha512.X86.Stream.finalize = 20 := by lit_decide

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hISp : NoSp (Impl.Sha512.X86.Stream.init iv)) (hISU : stackUse (Impl.Sha512.X86.Stream.init iv) = 0) :
    VG.Proof.Pbkdf2.Stream.X86.HashOK (VG.Proof.Pbkdf2.Stream.X86.sha512H D initN iv) where
  SH := SH
  Wb := 272
  hS := hS
  hD := hD
  hB := hB
  hDF := hD64
  hF := Nat.le_refl 64
  hD0 := hD0
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := show 272 ≤ 8 * 34 by decide
  hW := show 34 ≤ 64 by decide
  repr := hR ▸ sha512_repr iv
  init := hR ▸ Proof.Sha512.X86.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.X86.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86.Stream.Update.update_verified.2.2 }
  fin := VG.Proof.Pbkdf2.Stream.X86.finK_of_finKr <| Proof.Sha512.X86.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.2 }
  initSp := hISp
  updSp := VG.Proof.Pbkdf2.Stream.X86.sha512_updSp
  finSp := VG.Proof.Pbkdf2.Stream.X86.sha512_finSp
  initSU := by show stackUse (Impl.Sha512.X86.Stream.init iv) ≤ 20; rw [hISU]; decide
  updSU := by show stackUse Impl.Sha512.X86.Stream.update ≤ 20; rw [VG.Proof.Pbkdf2.Stream.X86.sha512_updSU]
  finSU := by show stackUse Impl.Sha512.X86.Stream.finalize ≤ 20; rw [VG.Proof.Pbkdf2.Stream.X86.sha512_finSU]

def sha384H : VG.Impl.Pbkdf2.Stream.X86.Hash := VG.Proof.Pbkdf2.Stream.X86.sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : VG.Impl.Pbkdf2.Stream.X86.Hash := VG.Proof.Pbkdf2.Stream.X86.sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : VG.Impl.Pbkdf2.Stream.X86.Hash := VG.Proof.Pbkdf2.Stream.X86.sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : VG.Impl.Pbkdf2.Stream.X86.Hash := VG.Proof.Pbkdf2.Stream.X86.sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : VG.Proof.Pbkdf2.Stream.X86.HashOK VG.Proof.Pbkdf2.Stream.X86.sha384H := VG.Proof.Pbkdf2.Stream.X86.sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)) (by lit_decide)
def sha512OK : VG.Proof.Pbkdf2.Stream.X86.HashOK VG.Proof.Pbkdf2.Stream.X86.sha512H' := VG.Proof.Pbkdf2.Stream.X86.sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm) (by decide) (by decide)
  (VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)) (by lit_decide)
def sha512_224OK : VG.Proof.Pbkdf2.Stream.X86.HashOK VG.Proof.Pbkdf2.Stream.X86.sha512_224H := VG.Proof.Pbkdf2.Stream.X86.sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide))
  (by lit_decide)
def sha512_256OK : VG.Proof.Pbkdf2.Stream.X86.HashOK VG.Proof.Pbkdf2.Stream.X86.sha512_256H := VG.Proof.Pbkdf2.Stream.X86.sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide))
  (by lit_decide)

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1`. -/
section

/-!
# SHA-1's streaming functions on x86 (32-bit), for every backend

SHA-1 has an implementation of its compression function for each variant of
its interface on x86 (`Variants/Sha1/X86/`), and its streaming `update` and
`finalize` made with each (`Sha1Stream`): `sha1OK` is `HashOK` for any of
them, with `vg_sha1_init`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha1.X86.Variants (hmacHash)

/-- SHA-1's streaming `update` and `finalize` made with one implementation of
its compression function, named with its suffix (e.g. `_shani`; nothing for
the baseline implementation), verified against their per-target contracts;
they keep `esp` and use at most 20 bytes of stack. -/
structure Sha1Stream where
  suffix : String
  upd : Prog isa
  fin : Prog isa
  updOK : Verified X86.target upd Proof.Sha1.updateX86
  finOK : Verified X86.target fin Proof.Sha1.finalizeX86
  updSp : NoSp upd
  finSp : NoSp fin
  updSU : stackUse upd ≤ 20
  finSU : stackUse fin ≤ 20

/-- SHA-1's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha1H (v : VG.Proof.Pbkdf2.Stream.X86.Sha1Stream) : Hash := VG.Proof.Sha1.X86.Variants.hmacHash v.suffix v.upd v.fin

theorem sha1_initSp : NoSp Impl.Sha1.X86.Stream.init := VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)
theorem sha1_initSU : stackUse Impl.Sha1.X86.Stream.init ≤ 20 := by lit_decide

/-- SHA-1's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha1OK (v : VG.Proof.Pbkdf2.Stream.X86.Sha1Stream) : VG.Proof.Pbkdf2.Stream.X86.HashOK (VG.Proof.Pbkdf2.Stream.X86.sha1H v) where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 20 ≤ 20 by decide
  hF := show 20 ≤ 64 by decide
  hD0 := show 0 < 20 by decide
  hS0 := show 0 < 84 by decide
  hSB := show 84 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Hmac.Generic.Common.sha1_repr
  init := Proof.Sha1.X86.Stream.init_verified
  upd := v.updOK
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := VG.Proof.Pbkdf2.Stream.X86.sha1_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := VG.Proof.Pbkdf2.Stream.X86.sha1_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha256`. -/
section

/-!
# SHA-256's streaming functions on x86 (32-bit), for every backend

SHA-256 has an implementation of its compression function for each variant
of its interface on x86 (`Variants/Sha256/X86/`), and its streaming `update`
and `finalize` made with each (`Sha256Stream`, verified for any initial hash
value): `sha256OK` is `HashOK` for any of them, with `vg_sha256_init`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash)

/-- SHA-256's streaming `update` and `finalize` made with one implementation
of its compression function, named with its suffix (e.g. `_shani`; nothing
for the baseline implementation), verified against their per-target
contracts, which hold from any initial hash value; they keep `esp` and use
at most 20 bytes of stack. -/
structure Sha256Stream where
  suffix : String
  upd : Prog isa
  fin : Prog isa
  updOK : Verified X86.target upd Proof.Sha256.updateX86
  finOK : Verified X86.target fin Proof.Sha256.finalizeX86
  updSp : NoSp upd
  finSp : NoSp fin
  updSU : stackUse upd ≤ 20
  finSU : stackUse fin ≤ 20

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha256H (v : VG.Proof.Pbkdf2.Stream.X86.Sha256Stream) : Hash := VG.Proof.Sha256.X86.Variants.hmacHash v.suffix v.upd v.fin

theorem sha256_initSp : NoSp Impl.Sha256.X86.Stream.init := VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)
theorem sha256_initSU : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide

/-- SHA-256's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha256OK (v : VG.Proof.Pbkdf2.Stream.X86.Sha256Stream) : VG.Proof.Pbkdf2.Stream.X86.HashOK (VG.Proof.Pbkdf2.Stream.X86.sha256H v) where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 32 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 32 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.X86.Stream.init_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := VG.Proof.Pbkdf2.Stream.X86.sha256_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := VG.Proof.Pbkdf2.Stream.X86.sha256_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224`. -/
section

/-!
# SHA-224's streaming functions on x86 (32-bit), for every backend

`HashOK` for SHA-224 (`sha224OK`), for any of SHA-256's backends on x86
(`Sha256Stream`): SHA-256's streaming functions from SHA-224's initial hash
value (`vg_sha224_init`, then the backend's `update` and `finalize`, whose
contracts hold from any initial hash value), with the digest the first 28
bytes of the final hash value.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha256.X86.Variants (hmacHash224)
open VG.Proof.Hmac.Generic.Common (readW_reloc bytesAt_reloc)

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha224H (v : VG.Proof.Pbkdf2.Stream.X86.Sha256Stream) : Hash := hmacHash224 v.suffix v.upd v.fin

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

theorem sha224_initSp : NoSp Impl.Sha256.X86.Stream.init224 := VG.Proof.Pbkdf2.Stream.X86.nosp_of (by lit_decide)
theorem sha224_initSU : stackUse Impl.Sha256.X86.Stream.init224 ≤ 20 := by lit_decide

/-- SHA-224's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha224OK (v : VG.Proof.Pbkdf2.Stream.X86.Sha256Stream) : VG.Proof.Pbkdf2.Stream.X86.HashOK (VG.Proof.Pbkdf2.Stream.X86.sha224H v) where
  SH := Spec.Hmac.sha224S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 28 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 28 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := VG.Proof.Pbkdf2.Stream.X86.sha224_repr
  init := Proof.Sha256.X86.Stream.init224_verified
  upd := v.updOK.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.updOK.2.2 }
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := VG.Proof.Pbkdf2.Stream.X86.sha224_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := VG.Proof.Pbkdf2.Stream.X86.sha224_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86

end
