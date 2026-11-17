module

import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Hmac.Stream.PPC64LE.Calls`, which this module and modules that import it used -/

section

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

end

end

/-!
# HMAC over any streaming hash function on PPC64LE: the hash function

`HashOK H` is what the proofs know of a hash function's streaming functions
`H`: they are verified against `initK`, `updK` and `finK` for the
specification's hash function `SH`, with the sizes of the code; they push at
most one frame; and a streaming state that represents whole blocks
represents them wherever its hash value is (`reloc`: its buffer is empty);
and what a streaming state represents depends only on its bytes (`congr`).
`callInit_ok`, `callUpd_ok` and `callFin_ok` are their calls, used as black
boxes through their proofs (`WP.callF`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- The sizes of a hash function's streaming code, and where HMAC saves our
caller's registers (`W` in `init` and `finalize`, `lsv` in `initLong`). -/
structure Dims (H : Hash) : Prop where
  N : 0 < H.N ∧ H.N ≤ 64
  so : H.W % 8 = 0 ∧ H.W ≤ 1024
  B : H.B = 64 ∨ H.B = 128
  lso : H.lsv % 8 = 0 ∧ H.lsv ≤ 1024

/-- The facts about a hash function's streaming functions. -/
structure HashOK (H : Hash) where
  SH : StreamingHash
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  dims : Dims H
  hN4 : H.N % 4 = 0
  hD0 : 0 < H.D
  hDB : H.D ≤ H.B
  hD4 : H.D % 4 = 0
  hDF : H.D ≤ H.FD
  hFD64 : H.FD ≤ 64
  /-- What the streaming `finalize` writes: the digest, then (SHA-384's and
  SHA-512/t's) the rest of SHA-512's final hash value. -/
  fh : List Byte → List Byte
  init : ∀ s, (initK H.S SH.Repr).pre s → ∃ t s', Exec isa H.initC s t s' ∧ abiPreserved s s' ∧
    (initK H.S SH.Repr).post s s'
  upd : ∀ s, (updK H.S H.W SH.Repr).pre s → ∃ t s', Exec isa H.updC s t s' ∧ abiPreserved s s' ∧
    (updK H.S H.W SH.Repr).post s s'
  fin : ∀ s, (finK H.S H.W H.FD SH.Repr fh).pre s → ∃ t s', Exec isa H.finC s t s' ∧
    abiPreserved s s' ∧ (finK H.S H.W H.FD SH.Repr fh).post s s'
  initFd : H.initC.fdepth ≤ 1
  updFd : H.updC.fdepth ≤ 1
  finFd : H.finC.fdepth ≤ 1
  initPf : pushFrames H.initC = true
  updPf : pushFrames H.updC = true
  finPf : pushFrames H.finC = true
  reloc : ∀ (m m' : Mem) (p q : Addr) (x : List Byte), x.length % H.B = 0 →
    (∀ i < H.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p x → SH.Repr m' q x
  congr : ∀ (m m' : Mem) (p : Addr) (x : List Byte),
    (∀ i < H.S, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → SH.Repr m p x → SH.Repr m' p x
  fhLen : ∀ x, (fh x).length = H.FD
  hashTake : ∀ x, SH.H.hash x = (fh x).take H.D

namespace HashOK

variable {H : Hash} (hH : HashOK H)

theorem hashLen (x : List Byte) : (hH.SH.H.hash x).length = H.D := by
  rw [hH.hashTake, List.length_take, hH.fhLen]; have := hH.hDF; omega_using [this]

include hH in
theorem hD64 : H.D ≤ 64 := by have := hH.hDF; have := hH.hFD64; omega_arith

/-- A callee's frames are in the 48 bytes below the stack pointer. -/
theorem frame48 {c : Prog isa} (hd : c.fdepth ≤ 1) {wr : List Region} {sp : Addr} {m m' : Mem}
    (h : Frame (wr ++ [below sp (48 * c.fdepth)]) m m') : Frame (wr ++ [below sp 48]) m m' :=
  Frame.below_mono h (by omega_using [hd]) (by omega_using [])

/-- The call of the streaming `init` on the state at `st`. -/
theorem callInit_ok {s : State} {st : Addr} (h3 : s.gpr .r3 = st)
    (hpre : 48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint ⟨st, H.S⟩)
    (hc : Covers [⟨st, H.S⟩] (s.rd ++ s.wr)) (hw : Covers [⟨st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩] ++ [below s.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa H.callInit s Q := by
  have c3 : s.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.callF (k := initK H.S hH.SH.Repr) hH.init (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (by simpa using hc) hw ?_ (by have := hH.initFd; omega_using [this]) hH.initPf
  · simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3]
    exact ⟨trivial, trivial, hpre.1, hpre.2⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [initK, State.withRegions_gpr, State.withRegions_mem, c3] at hpost
    exact hQ s' h₁ h₂ h₃ (frame48 hH.initFd h₄) hcs hpost

/-- The call of the streaming `update` on the state at `st`, with the `len`
bytes at `dat`, `count` in `r4` and the scratch space at `scr`. -/
theorem callUpd_ok {s : State} {st dat scr : Addr} {len : Nat}
    (h3 : s.gpr .r3 = st) (h5 : s.gpr .r5 = dat) (h6 : (s.gpr .r6).toNat = len)
    (h7 : s.gpr .r7 = scr)
    (hd₁ : Region.Disjoint ⟨st, H.S⟩ ⟨scr, H.W⟩) (hd₂ : Region.Disjoint ⟨dat, len⟩ ⟨st, H.S⟩)
    (hd₃ : Region.Disjoint ⟨dat, len⟩ ⟨scr, H.W⟩) (hsp : 48 ≤ s.sp.toNat)
    (hs₁ : (below s.sp 48).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp 48).Disjoint ⟨dat, len⟩)
    (hs₃ : (below s.sp 48).Disjoint ⟨scr, H.W⟩)
    (hc : Covers ([⟨dat, len⟩] ++ [⟨st, H.S⟩, ⟨scr, H.W⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩, ⟨scr, H.W⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩, ⟨scr, H.W⟩] ++ [below s.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa H.callUpd s Q := by
  have c3 : s.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = s.gpr .r4 := State.callEntry_gpr _ (by decide)
  have c5 : s.callEntry.gpr .r5 = dat := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : (s.callEntry.gpr .r6).toNat = len := by rw [State.callEntry_gpr _ (by decide), h6]
  have c7 : s.callEntry.gpr .r7 = scr := (State.callEntry_gpr _ (by decide)).trans h7
  refine WP.callF (k := updK H.S H.W hH.SH.Repr) hH.upd (rd := [⟨dat, len⟩])
    (wr := [⟨st, H.S⟩, ⟨scr, H.W⟩]) ?_ hc hw ?_ (by have := hH.updFd; omega_using [this]) hH.updPf
  · simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c5, c6, c7]
    exact ⟨trivial, trivial, hd₁, hd₂, hd₃, hsp, hs₁, hs₂, hs₃⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5,
      c6] at hpost
    exact hQ s' h₁ h₂ h₃ (frame48 hH.updFd h₄) hcs hpost

/-- The call of the streaming `finalize` on the state at `st`, with `count`
in `r4`, its digest to `o` and the scratch space at `scr`. -/
theorem callFin_ok {s : State} {st o scr : Addr}
    (h3 : s.gpr .r3 = st) (h5 : s.gpr .r5 = o) (h6 : s.gpr .r6 = scr)
    (hd₁ : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.FD⟩) (hd₂ : Region.Disjoint ⟨st, H.S⟩ ⟨scr, H.W⟩)
    (hd₃ : Region.Disjoint ⟨o, H.FD⟩ ⟨scr, H.W⟩) (hsp : 48 ≤ s.sp.toNat)
    (hs₁ : (below s.sp 48).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp 48).Disjoint ⟨o, H.FD⟩)
    (hs₃ : (below s.sp 48).Disjoint ⟨scr, H.W⟩)
    (hc : Covers [⟨st, H.S⟩, ⟨o, H.FD⟩, ⟨scr, H.W⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩, ⟨o, H.FD⟩, ⟨scr, H.W⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩, ⟨o, H.FD⟩, ⟨scr, H.W⟩] ++ [below s.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .r4 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem o H.FD = hH.fh m) → Q s') :
    WP isa H.callFin s Q := by
  have c3 : s.callEntry.gpr .r3 = st := (State.callEntry_gpr _ (by decide)).trans h3
  have c4 : s.callEntry.gpr .r4 = s.gpr .r4 := State.callEntry_gpr _ (by decide)
  have c5 : s.callEntry.gpr .r5 = o := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : s.callEntry.gpr .r6 = scr := (State.callEntry_gpr _ (by decide)).trans h6
  refine WP.callF (k := finK H.S H.W H.FD hH.SH.Repr hH.fh) hH.fin (rd := [])
    (wr := [⟨st, H.S⟩, ⟨o, H.FD⟩, ⟨scr, H.W⟩]) ?_ (by simpa using hc) hw ?_
    (by have := hH.finFd; omega_using [this]) hH.finPf
  · simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c5, c6]
    exact ⟨trivial, trivial, hd₁, hd₂, hd₃, hsp, hs₁, hs₂, hs₃⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4,
      c5] at hpost
    exact hQ s' h₁ h₂ h₃ (frame48 hH.finFd h₄) hcs hpost

end HashOK

end VG.Proof.Hmac.Stream.PPC64LE
