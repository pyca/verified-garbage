module

public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Hmac.Stream.RISCV64.Calls`, which this module and modules that import it used -/

section

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

end

end

/-!
# HMAC over any streaming hash function on RISC-V: the hash function

`HashOK H` is what the proofs know of a hash function's streaming functions
`H`: they are verified against `initK`, `updK` and `finK` for the
specification's hash function `SH`, with the sizes of the code; they use at
most `F` bytes of stack below the stack pointer (`sdepth`); a streaming
state that represents whole blocks represents them wherever its hash value
is (`reloc`: its buffer is empty); and what a streaming state represents
depends only on its bytes (`congr`). `callInit_ok`, `callUpd_ok` and
`callFin_ok` are their calls, used as black boxes through their proofs
(`WP.callAny`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- The facts about a hash function's streaming functions. -/
structure HashOK (H : Hash) where
  SH : StreamingHash
  hS : SH.stateBytes = H.S
  hD : SH.digestBytes = H.D
  hB : SH.H.blockSize = H.B
  hb : H.b = 6 ∨ H.b = 7
  hN : 0 < H.N ∧ H.N ≤ 64
  hD0 : 0 < H.D
  hD64 : H.D ≤ 64
  hF : H.F ≤ 1024
  init : ∀ s, (initK H.S SH.Repr).pre s → ∃ t s', Exec isa H.initC s t s' ∧ abiPreserved s s' ∧
    (initK H.S SH.Repr).post s s'
  upd : ∀ s, (updK H.S H.F SH.Repr).pre s → ∃ t s', Exec isa H.updC s t s' ∧ abiPreserved s s' ∧
    (updK H.S H.F SH.Repr).post s s'
  fin : ∀ s, (finK H.S H.F H.D SH.Repr SH.H.hash).pre s → ∃ t s', Exec isa H.finC s t s' ∧
    abiPreserved s s' ∧ (finK H.S H.F H.D SH.Repr SH.H.hash).post s s'
  initSd : sdepth H.initC ≤ H.F
  updSd : sdepth H.updC ≤ H.F
  finSd : sdepth H.finC ≤ H.F
  reloc : ∀ (m m' : Mem) (p q : Addr) (x : List Byte), x.length % H.B = 0 →
    (∀ i < H.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p x → SH.Repr m' q x
  congr : ∀ (m m' : Mem) (p : Addr) (x : List Byte),
    (∀ i < H.S, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → SH.Repr m p x → SH.Repr m' p x
  hashLen : ∀ x, (SH.H.hash x).length = H.D

namespace HashOK

variable {H : Hash} (hH : HashOK H)

include hH in
theorem hB64 : H.B = 64 ∨ H.B = 128 := by
  rcases hH.hb with h | h <;> simp [Hash.B, h]

include hH in
/-- A callee's frames are in the `F` bytes below the stack pointer. -/
theorem frameF {c : Prog isa} (hd : sdepth c ≤ H.F) {wr : List Region} {sp : Addr} {m m' : Mem}
    (h : Frame (wr ++ [below sp (sdepth c)]) m m') : Frame (wr ++ [below sp H.F]) m m' :=
  Frame.below_mono h hd (by have := hH.hF; omega_using [this])

/-- The call of the streaming `init` on the state at `st`. -/
theorem callInit_ok {s : State} {st : Addr} (h0 : s.gpr .a0 = st)
    (hc : Covers [⟨st, H.S⟩] (s.rd ++ s.wr)) (hw : Covers [⟨st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa H.callInit s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  refine WP.callAny (k := initK H.S hH.SH.Repr) hH.init (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (by simpa using hc) hw ?_ (by have := hH.initSd; have := hH.hF; omega_arith)
  · simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0]
    exact ⟨trivial, trivial⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [initK, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.initSd h₄) hcs hpost

/-- The call of the streaming `update` on the state at `st`, with the `len`
bytes at `dat` and `count` in `a1`. -/
theorem callUpd_ok {s : State} {st dat : Addr} {len : Nat}
    (h0 : s.gpr .a0 = st) (h2 : s.gpr .a2 = dat) (h3 : (s.gpr .a3).toNat = len)
    (hd : Region.Disjoint ⟨dat, len⟩ ⟨st, H.S⟩) (hal : s.sp.toNat % 16 = 0) (hsp : H.F ≤ s.sp.toNat)
    (hs₁ : (below s.sp H.F).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp H.F).Disjoint ⟨dat, len⟩)
    (hc : Covers ([⟨dat, len⟩] ++ [⟨st, H.S⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa H.callUpd s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.gpr .a1 := State.callEntry_gpr _ (by decide)
  have c2 : s.callEntry.gpr .a2 = dat := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : (s.callEntry.gpr .a3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3]
  refine WP.callAny (k := updK H.S H.F hH.SH.Repr) hH.upd (rd := [⟨dat, len⟩])
    (wr := [⟨st, H.S⟩]) ?_ hc hw ?_ (by have := hH.updSd; have := hH.hF; omega_arith)
  · simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2, c3]
    exact ⟨trivial, trivial, hd, hal, hsp, hs₁, hs₂⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      c3] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.updSd h₄) hcs hpost

/-- The call of the streaming `finalize` on the state at `st`, with `count`
in `a1` and its digest to `o`. -/
theorem callFin_ok {s : State} {st o : Addr}
    (h0 : s.gpr .a0 = st) (h2 : s.gpr .a2 = o)
    (hd : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.D⟩) (hal : s.sp.toNat % 16 = 0) (hsp : H.F ≤ s.sp.toNat)
    (hs₁ : (below s.sp H.F).Disjoint ⟨st, H.S⟩) (hs₂ : (below s.sp H.F).Disjoint ⟨o, H.D⟩)
    (hc : Covers [⟨st, H.S⟩, ⟨o, H.D⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, H.S⟩, ⟨o, H.D⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame ([⟨st, H.S⟩, ⟨o, H.D⟩] ++ [below s.sp H.F]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .a1 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem o H.D = hH.SH.H.hash m) → Q s') :
    WP isa H.callFin s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.gpr .a1 := State.callEntry_gpr _ (by decide)
  have c2 : s.callEntry.gpr .a2 = o := (State.callEntry_gpr _ (by decide)).trans h2
  refine WP.callAny (k := finK H.S H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin (rd := [])
    (wr := [⟨st, H.S⟩, ⟨o, H.D⟩]) ?_ (by simpa using hc) hw ?_
    (by have := hH.finSd; have := hH.hF; omega_arith)
  · simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c2]
    exact ⟨trivial, trivial, hd, hal, hsp, hs₁, hs₂⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1,
      c2] at hpost
    exact hQ s' h₁ h₂ h₃ (frameF hH hH.finSd h₄) hcs hpost

/-- A streaming state representing whole blocks survives writes outside its
hash value. -/
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {x : List Byte}
    (hx : x.length % H.B = 0) (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) (hr : hH.SH.Repr m p x) :
    hH.SH.Repr m' p x :=
  hH.reloc m m' p p x hx (fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd
    (by have : H.N ≤ 64 := hH.hN.2; show H.N ≤ 2 ^ 64; omega_using [this]) hi) hr

end HashOK

end VG.Proof.Hmac.Stream.RISCV64
