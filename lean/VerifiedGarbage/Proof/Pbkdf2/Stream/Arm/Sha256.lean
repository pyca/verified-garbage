import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Sha1.Arm.Shared
import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Sha512.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any streaming hash function: the 32-bit ARM contracts

The contracts the proofs are written against, as on x86-64 and AArch64
(`Proof/Hmac/Generic/AArch64/Hash.lean`).

* `initK`, `updK` and `finK` are the 32-bit ARM contracts of a hash
  function's streaming `init`, `update` and `finalize` (`Proof.Sha1.initArm`
  and the others), with the sizes and the representation of the streaming
  state as parameters. Under AAPCS `count` is in `r2:r3`, and `update`'s
  `data`, `len` and `scratch` and `finalize`'s `out` and `scratch` are
  stack arguments.
* `initG`, `finG` and `iterG` are those of our functions, which push up to
  16 bytes of stack (the stack arguments of the functions they call), which
  no buffer overlaps; the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`, which imply them
  (`Contract.Implies`).
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 16 bytes below the stack pointer. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- The 64-bit `count` argument, in `r2:r3` (AAPCS: the low word in `r2`). -/
def count (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), S⟩] ∧ (s.gpr .r0).toNat + S ≤ 2 ^ 32
  post s s' := R s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), S⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), Wb⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + S ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + Wb ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem (State.addr (s.gpr .r0)) m → VG.Proof.Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 m.length →
    R s'.mem (State.addr (s.gpr .r0)) (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), S⟩
    let out : Region := ⟨State.addr (stackArg s 0), F⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), Wb⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + S ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + F ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + Wb ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, R s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    VG.Proof.Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem (State.addr (stackArg s 0)) F).take D = hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initScratchContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), S.stateBytes⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), S.stateBytes⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    (s.gpr .r3).toNat ≤ S.H.blockSize ∧ s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint inner ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint outer ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint key ∧
    (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    S.Repr s'.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) ∧
      S.Repr s'.mem (State.addr (s.gpr .r1)) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeScratchContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), S.stateBytes⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), S.stateBytes⟩
    let out : Region := ⟨State.addr (stackArg s 0), S.digestBytes⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [outer, args] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint inner ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint outer ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint out ∧
    (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad ++ text) →
    VG.Proof.Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (State.addr (s.gpr .r1)) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (stackArg s 0)) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `iterate(key, u, n, t, scratch)`: `VG.Spec.Pbkdf2.iterateContract`. -/
def iterG : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 2 * S.stateBytes⟩
    let u : Region := ⟨State.addr (s.gpr .r1), S.digestBytes⟩
    let t : Region := ⟨State.addr (s.gpr .r3), S.digestBytes⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    args.Disjoint t ∧ args.Disjoint scratch ∧
    (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint key ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint u ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint t ∧ (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + 2 * S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.digestBytes ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ k0, k0.length = S.H.blockSize →
    S.Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) →
    S.Repr s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (s.gpr .r3)) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (s.gpr .r2).toNat
        (bytesAt s.mem (State.addr (s.gpr .r1)) S.digestBytes)
        (bytesAt s.mem (State.addr (s.gpr .r3)) S.digestBytes)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Pbkdf2.Stream.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: the functions we call

As on x86-64 and AArch64 (`Proof/Hmac/Generic/AArch64/Hash.lean`): `HashOK H`
is what the proofs know of the hash function `H`: its streaming functions are
verified against `initK`, `updK` and `finK` and have no frames, the
representation of its streaming state is determined by the state's bytes, and
its sizes are small.

`init` is called with `WP.callCalls`. `update` and `finalize` are called in
a frame that pushes their stack arguments (`WP.frame`), then sets the count
in `r2:r3`: `upd_frame` and `fin_frame` run such a frame, from the state
before its push. A frame writes the 16 bytes below the stack pointer, which
`After` lets change. `init_rel`, `upd_rel` and `fin_rel` relate two runs of
them (`RelCT.call`, `RelCT.frame`).
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.MdStream.Arm (Upd WP.cons op2_imm op2_reg)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's 32-bit ARM functions, verified. `Wb` is the
scratch space their contracts use, at most the `8 W` bytes we give them. -/
structure HashOK (H : Hash) where
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
  init : Verified Arm.target H.initC (VG.Proof.Pbkdf2.Stream.Arm.initK H.S SH.Repr)
  upd : Verified Arm.target H.updC (VG.Proof.Pbkdf2.Stream.Arm.updK H.S Wb SH.Repr)
  fin : Verified Arm.target H.finC (VG.Proof.Pbkdf2.Stream.Arm.finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initNF : H.initC.noFrames = true
  updNF : H.updC.noFrames = true
  finNF : H.finC.noFrames = true

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK H)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [VG.Proof.Pbkdf2.Stream.Arm.below s]) s.mem s'.mem

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .r0 = s.gpr .r0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .r1 = s.gpr .r1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .r2 = s.gpr .r2 := State.callEntry_gpr s (by decide)
@[simp] theorem ce3 (s : State) : s.callEntry.gpr .r3 = s.gpr .r3 := State.callEntry_gpr s (by decide)

theorem wp_movw {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

/-! ## `init` -/

theorem init_call {s : State} {st : BitVec 32} (h0 : s.gpr .r0 = st) (hn : st.toNat + H.S ≤ 2 ^ 32)
    (hc : Covers [⟨State.addr st, H.S⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.Arm.After s [⟨State.addr st, H.S⟩] s' → hH.SH.Repr s'.mem (State.addr st) [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.callCalls (k := VG.Proof.Pbkdf2.Stream.Arm.initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨State.addr st, H.S⟩]) ?_
    (VG.Proof.Pbkdf2.Stream.Arm.covers_wr hc) hc ?_ hH.initNF
  · exact ⟨rfl, by simp [h0], by simpa [h0] using hn⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ _ hpost
    refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Stream.Arm.frame_app h₄⟩ ?_
    simpa [VG.Proof.Pbkdf2.Stream.Arm.initK, h0] using hpost

/-! ## The frames

A frame of `n` bytes (8 or 16) stores its words below the stack pointer, in
`below s`, where the callee finds its stack arguments. -/

/-- `x - k + i` (for `i ≤ k ≤ x`) widened to 64 bits. -/
theorem addr_sub_add {x : BitVec 32} {k i : Nat} (hk : k ≤ x.toNat) (hi : i ≤ k) :
    State.addr (x - BitVec.ofNat 32 k + BitVec.ofNat 32 i) =
      State.addr x - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := x.toNat) (by omega_nat),
    show 2 ^ 32 - k + x.toNat = 2 ^ 32 + (x.toNat - k) by omega_nat, Nat.add_mod_left,
    show 2 ^ 64 - k + x.toNat = 2 ^ 64 + (x.toNat - k) by omega_nat, Nat.add_mod_left]
  omega_nat

/-- `x - k` (for `k ≤ x`) widened to 64 bits. -/
theorem addr_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    State.addr (x - BitVec.ofNat 32 k) = State.addr x - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := k) (by omega_nat),
    Nat.mod_eq_of_lt (a := x.toNat) (by omega_nat),
    show 2 ^ 32 - k + x.toNat = 2 ^ 32 + (x.toNat - k) by omega_nat, Nat.add_mod_left,
    show 2 ^ 64 - k + x.toNat = 2 ^ 64 + (x.toNat - k) by omega_nat, Nat.add_mod_left]
  omega_nat

/-- Bytes at two offsets from a base that do not overlap. -/
theorem sep_off (b : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32)
    (he : e + k < 2 ^ 32) : Mem.Sep (b + BitVec.ofNat 64 d) n (b + BitVec.ofNat 64 e) k := Offset.sep b h (by omega_nat) (by omega_nat)

/-- Bytes at a base and at an offset from it that do not overlap. -/
theorem sep_base_off (b : Addr) {e n k : Nat} (h : n ≤ e) (he : e + k < 2 ^ 32) :
    Mem.Sep b n (b + BitVec.ofNat 64 e) k := Offset.sep_base b h (by omega_nat)

/-- Bytes at an offset from a region's base, in it. -/
theorem contains_off (b : Addr) {len d n : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 64) :
    Region.Contains ⟨b, len⟩ (b + BitVec.ofNat 64 d) n := Offset.contains_base b h (by omega_nat)

/-- A 16-bit count in `r2:r3`. -/
theorem count_movw {t : State} {c : Nat} (hc : c < 2 ^ 16) (h2 : t.gpr .r2 = (BitVec.ofNat 16 c).setWidth 32)
    (h3 : t.gpr .r3 = 0) : VG.Proof.Pbkdf2.Stream.Arm.count t = BitVec.ofNat 64 c := by
  simp only [VG.Proof.Pbkdf2.Stream.Arm.count, h2, h3]
  apply BitVec.eq_of_toNat_eq
  have z : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ofNat, z, Nat.zero_shiftLeft, Nat.zero_or]
  omega_nat

/-! ## `update`, in its frame -/

/-- What a framed call of `update` needs of the state before its push: the
state at `st` in `r0`, the count in `r2:r3`, and `len` bytes of data at `d`
and the scratch space at `sc` in `r1`, `r7` and `r10`; the regions the
callee may read and write; that they are disjoint as it needs, and from the
16 bytes below the stack pointer; and that none of them wraps around. -/
structure UpdArgs (s : State) (st d sc : BitVec 32) (len : Nat) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = d
  r7 : s.gpr .r7 = BitVec.ofNat 32 len
  r10 : s.gpr .r10 = sc
  hlen : len < 2 ^ 16
  sp16 : 16 ≤ s.sp.toNat
  cd : Covers [⟨State.addr d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr st, H.S⟩
  d_sc : Region.Disjoint ⟨State.addr d, len⟩ ⟨State.addr sc, hH.Wb⟩
  b_st : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr st, H.S⟩
  b_d : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr d, len⟩
  b_sc : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr sc, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  nd : d.toNat + len ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The four words `update`'s frame pushes. -/
abbrev upd4 : List Reg := [.r1, .r7, .r10, .r12]

theorem e16 : BitVec.ofNat 32 (4 * upd4.length) = 16 := rfl

/-- The regions `update` is given: the data and its stack arguments, the state and the scratch space. -/
abbrev UpdArgs.rd (sp : BitVec 32) (d : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr d, len⟩, ⟨State.addr sp - 16, 12⟩]
abbrev UpdArgs.wr (st sc : BitVec 32) : List Region := [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩]

namespace UpdArgs
variable {hH} {s : State} {st d sc : BitVec 32} {len : Nat} (h : VG.Proof.Pbkdf2.Stream.Arm.UpdArgs hH s st d sc len)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := VG.Proof.Pbkdf2.Stream.Arm.addr_sub h.sp16
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 4 := VG.Proof.Pbkdf2.Stream.Arm.addr_sub_add h.sp16 (by decide)
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 8 := by
  rw [BitVec.add_assoc]; exact VG.Proof.Pbkdf2.Stream.Arm.addr_sub_add (k := 16) (i := 8) h.sp16 (by decide)
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 12 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact VG.Proof.Pbkdf2.Stream.Arm.addr_sub_add (k := 16) (i := 12) h.sp16 (by decide)

/-- The memory after the push. -/
theorem pmem : (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) d).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 4)
      (BitVec.ofNat 32 len)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 8) sc).writeW
      (State.addr s.sp - 16 + BitVec.ofNat 64 12) (s.gpr .r12) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * upd4.length)) [s.gpr .r1, s.gpr .r7, s.gpr .r10, s.gpr .r12] = _
  rw [VG.Proof.Pbkdf2.Stream.Arm.e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r1, h.r7, h.r10]

omit h in
theorem psp : (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).sp = s.sp - 16 := by rw [pushed_sp, VG.Proof.Pbkdf2.Stream.Arm.e16]

/-- The stack arguments, in a state whose memory and stack pointer are those after the push. -/
theorem sa (T : State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  simp only [stackArgAddr, ht]
  exact VG.Proof.Pbkdf2.Stream.Arm.addr_sub_add (k := 16) h.sp16 (by omega_nat)

theorem sa0 (T : State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem) : stackArg T 0 = d := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem, Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide), show 4 * 0 = 0 from rfl, BitVec.add_zero,
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem) :
    stackArg T 1 = BitVec.ofNat 32 len := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem, Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide), show 4 * 1 = 4 from rfl,
    Mem.readW_writeW_self32]

theorem arg2 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem) : stackArg T 2 = sc := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem, Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 2 = 8 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [VG.Proof.Pbkdf2.Stream.Arm.below s] s.mem (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (VG.Proof.Pbkdf2.Stream.Arm.below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; exact VG.Proof.Pbkdf2.Stream.Arm.contains_off _ (by omega_nat) (by decide)
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
    (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.rd s.sp d len) (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.wr hH st sc)).sp = s.sp - 16 := VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.psp
omit h in
theorem vmem : ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.rd s.sp d len) (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.wr hH st sc)).mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem := rfl

theorem hlen' : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; have := h.hlen; omega_nat

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 12⟩ (VG.Proof.Pbkdf2.Stream.Arm.below s) := by
  intro x hx; simp only [Region.Contains] at hx ⊢; omega_nat

theorem pre : (VG.Proof.Pbkdf2.Stream.Arm.updK H.S hH.Wb hH.SH.Repr).pre ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.rd s.sp d len) (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.wr hH st sc)) := by
  simp only [VG.Proof.Pbkdf2.Stream.Arm.updK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr,
    h.arg0 _ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vsp VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vmem, h.arg1 _ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vsp VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vmem, h.arg2 _ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vsp VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vmem, h.sa0 _ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vsp, h.r0, h.hlen']
  refine ⟨trivial, trivial, h.st_sc, h.d_st, h.d_sc, (h.b_st.sub_left VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.argsSub), (h.b_sc.sub_left VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.argsSub),
    h.nst, h.nd, h.nsc, ?_⟩
  rw [VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.vsp, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.rd s.sp d len ++ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.wr hH st sc) ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).rd ++ (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, VG.Proof.Pbkdf2.Stream.Arm.e16]
  rcases hr with (rfl | rfl) | (rfl | rfl)
  · obtain ⟨r', hr', hc'⟩ := h.cd x n' ⟨_, List.mem_singleton_self _, hcn⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact ⟨r', List.mem_append_left _ hr', hc'⟩
    · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a0]; simp only [Region.Contains, VG.Proof.Pbkdf2.Stream.Arm.upd4, List.length_cons, List.length_nil] at hcn ⊢; omega_nat
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (VG.Proof.Pbkdf2.Stream.Arm.UpdArgs.wr hH st sc) (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end UpdArgs

/-- After a frame of `rs` of `n` bytes around a call that keeps the regions
and the stack pointer. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [VG.Proof.Pbkdf2.Stream.Arm.below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem) (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    VG.Proof.Pbkdf2.Stream.Arm.After s ws (popped .r1 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr1, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (VG.Proof.Pbkdf2.Stream.Arm.frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (VG.Proof.Pbkdf2.Stream.Arm.frame_app (ws' := [VG.Proof.Pbkdf2.Stream.Arm.below s]) hf)

theorem upd_frame {s : State} {st d sc : BitVec 32} {len : Nat} (h : VG.Proof.Pbkdf2.Stream.Arm.UpdArgs hH s st d sc len)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.Arm.After s [⟨State.addr st, H.S⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → VG.Proof.Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (State.addr st) (m ++ bytesAt s.mem (State.addr d) len)) → Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Stream.Arm.upd4) (.call H.updN H.updC) (.pop .r1 16)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := VG.Proof.Pbkdf2.Stream.Arm.upd4) (r := .r1) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.callCalls (k := VG.Proof.Pbkdf2.Stream.Arm.updK H.S hH.Wb hH.SH.Repr) hH.upd.1 h.pre h.cov h.covW ?_ hH.updNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : VG.Proof.Pbkdf2.Stream.Arm.count ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)) = VG.Proof.Pbkdf2.Stream.Arm.count s := by
    simp only [VG.Proof.Pbkdf2.Stream.Arm.count, State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce2, VG.Proof.Pbkdf2.Stream.Arm.ce3, pushed_gpr]
  simp only [VG.Proof.Pbkdf2.Stream.Arm.updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr, h.r0,
    h.arg0 _ UpdArgs.vsp UpdArgs.vmem, h.arg1 _ UpdArgs.vsp UpdArgs.vmem, h.hlen', vc] at hpost
  refine hQ _ (VG.Proof.Pbkdf2.Stream.Arm.after_frame h.fP hrd hwr hsp hf hcs) fun m hr hcm => ?_
  have hs : ∀ r ∈ [VG.Proof.Pbkdf2.Stream.Arm.below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem (State.addr st) m :=
    hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr
  have hd : bytesAt (pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).mem (State.addr d) len = bytesAt s.mem (State.addr d) len := by
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    exact h.fP.bytes (R := ⟨State.addr d, len⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.b_d.symm) (by show len ≤ 2 ^ 64; have := h.hlen; omega_nat)
      (List.mem_range.mp hi)
  rw [popped_mem, ← hd]
  exact hpost m hr' hcm

/-! ## `finalize`, in its frame -/

/-- What a framed call of `finalize` needs of the state before its push:
the state at `st` in `r0`, the count in `r2:r3`, and `out` at `o` and the
scratch space at `sc` in `r1` and `r12`, as for `update`. -/
structure FinArgs (s : State) (st o sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = o
  r12 : s.gpr .r12 = sc
  sp16 : 16 ≤ s.sp.toNat
  cw : Covers [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr o, H.F⟩
  st_sc : Region.Disjoint ⟨State.addr st, H.S⟩ ⟨State.addr sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨State.addr o, H.F⟩ ⟨State.addr sc, hH.Wb⟩
  b_st : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr st, H.S⟩
  b_o : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr o, H.F⟩
  b_sc : (VG.Proof.Pbkdf2.Stream.Arm.below s).Disjoint ⟨State.addr sc, hH.Wb⟩
  nst : st.toNat + H.S ≤ 2 ^ 32
  no : o.toNat + H.F ≤ 2 ^ 32
  nsc : sc.toNat + hH.Wb ≤ 2 ^ 32

/-- The two words `finalize`'s frame pushes. -/
abbrev fin2 : List Reg := [.r1, .r12]

theorem e8 : BitVec.ofNat 32 (4 * fin2.length) = 8 := rfl

/-- The regions `finalize` is given: its stack arguments, the state, `out` and the scratch space. -/
abbrev FinArgs.rd (sp : BitVec 32) : List Region := [⟨State.addr sp - 8, 8⟩]
abbrev FinArgs.wr (st o sc : BitVec 32) : List Region :=
  [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩]

namespace FinArgs
variable {hH} {s : State} {st o sc : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.Arm.FinArgs hH s st o sc)
include h

theorem a8 : State.addr (s.sp - 8) = State.addr s.sp - 8 := VG.Proof.Pbkdf2.Stream.Arm.addr_sub (k := 8) (by have := h.sp16; omega_nat)
theorem a4 : State.addr (s.sp - 8 + 4) = State.addr s.sp - 8 + BitVec.ofNat 64 4 :=
  VG.Proof.Pbkdf2.Stream.Arm.addr_sub_add (k := 8) (i := 4) (by have := h.sp16; omega_nat) (by decide)

theorem pmem : (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem =
    (s.mem.writeW (State.addr s.sp - 8) o).writeW (State.addr s.sp - 8 + BitVec.ofNat 64 4) sc := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * fin2.length)) [s.gpr .r1, s.gpr .r12] = _
  rw [VG.Proof.Pbkdf2.Stream.Arm.e8]
  show (s.mem.writeW (State.addr (s.sp - 8)) _).writeW (State.addr (s.sp - 8 + 4)) _ = _
  rw [h.a8, h.a4, h.r1, h.r12]

omit h in
theorem psp : (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).sp = s.sp - 8 := by rw [pushed_sp, VG.Proof.Pbkdf2.Stream.Arm.e8]

theorem sa0 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 0 = State.addr s.sp - 8 := by
  simp only [stackArgAddr, ht]
  rw [BitVec.add_zero]; exact h.a8

theorem sa1 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 1 = State.addr s.sp - 8 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr, ht]; exact h.a4

theorem arg0 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem) : stackArg T 0 = o := by
  rw [stackArg, h.sa0 T ht, hm, h.pmem, Mem.readW_writeW_sep (VG.Proof.Pbkdf2.Stream.Arm.sep_base_off _ (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem) : stackArg T 1 = sc := by
  rw [stackArg, h.sa1 T ht, hm, h.pmem, Mem.readW_writeW_self32]

theorem fP : Frame [VG.Proof.Pbkdf2.Stream.Arm.below s] s.mem (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem := by
  rw [h.pmem]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, show (16 : Addr) = BitVec.ofNat 64 16 from rfl,
      Offset.sub_ofNat_sub_sub_ofNat _ (by omega_nat), BitVec.toNat_ofNat]; omega_nat
  · simp only [Region.Contains]
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, show (16 : Addr) = BitVec.ofNat 64 16 from rfl,
      Offset.add_sub_comm, Offset.sub_ofNat_sub_sub_ofNat _ (by omega_nat)]
    decide

omit h in
theorem vsp : ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.rd s.sp) (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.wr hH st o sc)).sp = s.sp - 8 := VG.Proof.Pbkdf2.Stream.Arm.FinArgs.psp
omit h in
theorem vmem : ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.rd s.sp) (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.wr hH st o sc)).mem = (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem := rfl

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (VG.Proof.Pbkdf2.Stream.Arm.below s) :=
  Offset.sub_below _ (a := 8) (b := 16) (by omega_nat) (by omega_nat)

theorem pre : (VG.Proof.Pbkdf2.Stream.Arm.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
    ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).callEntry.withRegions (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.rd s.sp) (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.wr hH st o sc)) := by
  simp only [VG.Proof.Pbkdf2.Stream.Arm.finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr,
    h.arg0 _ VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vsp VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vmem, h.arg1 _ VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vsp VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vmem, h.sa0 _ VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vsp, h.r0]
  refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, (h.b_st.sub_left VG.Proof.Pbkdf2.Stream.Arm.FinArgs.argsSub), (h.b_o.sub_left VG.Proof.Pbkdf2.Stream.Arm.FinArgs.argsSub),
    (h.b_sc.sub_left VG.Proof.Pbkdf2.Stream.Arm.FinArgs.argsSub), h.nst, h.no, h.nsc, ?_⟩
  rw [VG.Proof.Pbkdf2.Stream.Arm.FinArgs.vsp, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.rd s.sp ++ VG.Proof.Pbkdf2.Stream.Arm.FinArgs.wr hH st o sc) ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).rd ++ (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, VG.Proof.Pbkdf2.Stream.Arm.e8]
  rcases hr with rfl | (rfl | rfl | rfl)
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a8]; simp only [Region.Contains, VG.Proof.Pbkdf2.Stream.Arm.fin2, List.length_cons, List.length_nil] at hcn ⊢; omega_nat
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (VG.Proof.Pbkdf2.Stream.Arm.FinArgs.wr hH st o sc) (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end FinArgs

theorem fin_frame {s : State} {st o sc : BitVec 32} (h : VG.Proof.Pbkdf2.Stream.Arm.FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Stream.Arm.After s [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → m.length < 2 ^ 64 → VG.Proof.Pbkdf2.Stream.Arm.count s = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (State.addr o) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push VG.Proof.Pbkdf2.Stream.Arm.fin2) (.call H.finN H.finC) (.pop .r1 8)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := VG.Proof.Pbkdf2.Stream.Arm.fin2) (r := .r1) rfl (by show 8 ≤ s.sp.toNat; omega_nat) (by decide) ?_
  refine WP.callCalls (k := VG.Proof.Pbkdf2.Stream.Arm.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 h.pre h.cov h.covW ?_ hH.finNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : VG.Proof.Pbkdf2.Stream.Arm.count ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)) = VG.Proof.Pbkdf2.Stream.Arm.count s := by
    simp only [VG.Proof.Pbkdf2.Stream.Arm.count, State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce2, VG.Proof.Pbkdf2.Stream.Arm.ce3, pushed_gpr]
  simp only [VG.Proof.Pbkdf2.Stream.Arm.finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr, h.r0,
    h.arg0 _ FinArgs.vsp FinArgs.vmem, vc] at hpost
  refine hQ _ (VG.Proof.Pbkdf2.Stream.Arm.after_frame h.fP hrd hwr hsp hf hcs) fun m hr hl hcm => ?_
  have hs : ∀ r ∈ [VG.Proof.Pbkdf2.Stream.Arm.below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).mem (State.addr st) m :=
    hH.repr _ _ _ _ _ (fun i hi => h.fP.bytes (R := ⟨State.addr st, H.S⟩) hs
      (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr
  rw [popped_mem]
  exact hpost m hr' hl hcm

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`); a frame around it, when the
stack pointer is the same in both (`RelCT.frame`). -/

theorem push_eq {rs : List Reg} {s a : State} (hrs : regList rs = true) (h : isa.push (.push rs) s = some a) :
    a = pushed rs s := by
  rw [push_pushed hrs (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

include hH in
theorem init_rel {P : State → State → Prop} {st : BitVec 32}
    (h : ∀ s s', P s s' → s.gpr .r0 = st ∧ s'.gpr .r0 = st ∧ st.toNat + H.S ≤ 2 ^ 32 ∧
      Covers [⟨State.addr st, H.S⟩] s.wr ∧ Covers [⟨State.addr st, H.S⟩] s'.wr) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨State.addr st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', hn, c, c'⟩ := h s s' hp
  refine ⟨⟨rfl, by simp [d], by simpa [d] using hn⟩, ⟨rfl, by simp [d'], by simpa [d'] using hn⟩, ?_,
    VG.Proof.Pbkdf2.Stream.Arm.covers_wr c, c, VG.Proof.Pbkdf2.Stream.Arm.covers_wr c', c'⟩
  simp only [VG.Proof.Pbkdf2.Stream.Arm.initK, State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce0, d, d']

theorem upd_rel {P : State → State → Prop} {sp : BitVec 32} {st d sc : BitVec 32} {len : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Stream.Arm.UpdArgs hH s st d sc len ∧ VG.Proof.Pbkdf2.Stream.Arm.UpdArgs hH s' st d sc len ∧ VG.Proof.Pbkdf2.Stream.Arm.count s = VG.Proof.Pbkdf2.Stream.Arm.count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push VG.Proof.Pbkdf2.Stream.Arm.upd4) (.call H.updN H.updC) (.pop .r1 16)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.upd.1 hH.upd.2.1 (UpdArgs.rd sp d len) (UpdArgs.wr hH st sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨u, u', hc, e, e'⟩ := h s s' hp
  rw [VG.Proof.Pbkdf2.Stream.Arm.push_eq rfl pa, VG.Proof.Pbkdf2.Stream.Arm.push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : UpdArgs.rd s.sp d len = UpdArgs.rd s'.sp d len := by rw [v]
  have t1 : ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s).callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)).sp =
    s.sp - 16 := UpdArgs.psp
  have t2 : ((pushed VG.Proof.Pbkdf2.Stream.Arm.upd4 s').callEntry.withRegions (UpdArgs.rd s.sp d len) (UpdArgs.wr hH st sc)).sp =
    s'.sp - 16 := UpdArgs.psp
  refine ⟨u.pre, hv' ▸ u'.pre, ?_, u.cov, u.covW, hv' ▸ u'.cov, u'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [VG.Proof.Pbkdf2.Stream.Arm.updK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr, u.r0, u'.r0]
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce3, pushed_gpr, c3]
  · rw [u.arg0 _ t1 rfl, u'.arg0 _ t2 rfl]
  · rw [u.arg1 _ t1 rfl, u'.arg1 _ t2 rfl]
  · rw [u.arg2 _ t1 rfl, u'.arg2 _ t2 rfl]

theorem fin_rel {P : State → State → Prop} {sp : BitVec 32} {st o sc : BitVec 32}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Stream.Arm.FinArgs hH s st o sc ∧ VG.Proof.Pbkdf2.Stream.Arm.FinArgs hH s' st o sc ∧ VG.Proof.Pbkdf2.Stream.Arm.count s = VG.Proof.Pbkdf2.Stream.Arm.count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push VG.Proof.Pbkdf2.Stream.Arm.fin2) (.call H.finN H.finC) (.pop .r1 8)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.fin.1 hH.fin.2.1 (FinArgs.rd sp) (FinArgs.wr hH st o sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨f, f', hc, e, e'⟩ := h s s' hp
  rw [VG.Proof.Pbkdf2.Stream.Arm.push_eq rfl pa, VG.Proof.Pbkdf2.Stream.Arm.push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : FinArgs.rd s.sp = FinArgs.rd s'.sp := by rw [v]
  have t1 : ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s.sp - 8 := FinArgs.psp
  have t2 : ((pushed VG.Proof.Pbkdf2.Stream.Arm.fin2 s').callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s'.sp - 8 := FinArgs.psp
  refine ⟨f.pre, hv' ▸ f'.pre, ?_, f.cov, f.covW, hv' ▸ f'.cov, f'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [VG.Proof.Pbkdf2.Stream.Arm.finK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce0, pushed_gpr, f.r0, f'.r0]
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Stream.Arm.ce3, pushed_gpr, c3]
  · rw [f.arg0 _ t1 rfl, f'.arg0 _ t2 rfl]
  · rw [f.arg1 _ t1 rfl, f'.arg1 _ t2 rfl]

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The taint in which the registers `rs` and the first `n` bytes of stack
arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.Arm.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, argLen := n }

/-- The first `4 j` bytes of stack arguments agree when their first `j` words do. -/
theorem argMem_of {s₁ s₂ : State} {j : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * j ≤ 2 ^ 32)
    (h : ∀ i < j, stackArg s₁ i = stackArg s₂ i) :
    ∀ k < 4 * j, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  intro k hk
  have e : ∀ s : State, s.sp.toNat + 4 * j ≤ 2 ^ 32 →
      VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := fun s hs => by
    simp only [VG.Arm.Taint.argByte, stackArgAddr]
    rw [addr_add (by omega_nat), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_nat
  rw [e s₁ hf, e s₂ (hsp ▸ hf), Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_nat)),
    Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_nat))]
  exact congrArg _ (h _ (by omega_nat))

theorem agree_argTaint {rs : List Reg} {n : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.sp = s₂.sp)
    (hw₁ : s₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, n⟩ r)
    (hw₂ : s₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, n⟩ r)
    (hm : ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k)) :
    VG.Arm.Taint.Agree (VG.Proof.Pbkdf2.Stream.Arm.argTaint rs n) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₁,
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₂,
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp _ := hsp
  argMem := hm

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.Arm.Taint.Agree τ s s')
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

end VG.Proof.Pbkdf2.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common`. -/
section

/-!
# Calls of a streaming hash function on 32-bit ARM: the byte loops

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`, with the byte-list lemmas
of `Proof/Hmac/Generic/Common.lean`): the byte copy (`copy`) and the
exclusive-or of `U` into `T`, which the whole of PBKDF2 uses. Each counts `r8`
up from 0 and `r9` down to 0 with `subs`, and branches on its result. Addresses are 32 bits, zero-extended: every buffer the loops touch lies
below 2³², so byte `k` of a buffer at `p + o` is at `State.addr p + o + k`.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons op2_imm op2_reg wp_mov wp_add wp_subs wp_ldrb wp_strb
  eval_ne sub_beq sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint xorBytes_snoc
  xorBytes_length' InRegions.right' add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem ofNat_succ32 (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem movw_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

/-- Byte `k` of the buffer at `a + o`, as a loop addresses it. -/
theorem addr3 {a : BitVec 32} {k o : Nat} (h : a.toNat + o + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k + BitVec.ofNat 32 o) = State.addr a + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_nat), BitVec.ofNat_add, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 k)]

/-- The flags after counting `r9` down from `n - k` to `n - (k + 1)`. -/
theorem left_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (n - (k + 1) = 0) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_nat) (by decide)]
  simp only [decide_eq_decide]; omega_nat

theorem left_val {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_nat), Nat.sub_sub]

/-- The registers the loops write. -/
abbrev clob : List Reg := [.r1, .r2, .r8, .r9, .r12]

/-- The registers `copy` writes. -/
abbrev cclob : List Reg := [.r2, .r8, .r9, .r12]

theorem nm {r : Reg} {l : List Reg} (h : r ∉ l) (x : Reg) (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `ne` that runs its body `n > 0` times, each run
ending with the flags of `n - (k + 1) = 0`. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.z = decide (n - (k + 1) = 0))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (n - (k + 1) = 0)) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp; omega_nat, n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-! ## `copy` -/

/-- After `k` bytes of a `copy` of `n` bytes from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.Arm.cclob, t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 32 k
  r9 : t.gpr .r9 = BitVec.ofNat 32 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.Arm.cclob, t.gpr r = s.gpr r
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ∉ VG.Proof.Pbkdf2.Stream.Arm.cclob) (hd : dst ∉ VG.Proof.Pbkdf2.Stream.Arm.cclob)
    {so d n : Nat} (hso : so < 4096) (hdo : d < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, n⟩
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      VG.Proof.Pbkdf2.Stream.Arm.Copied s (State.addr (s.gpr dst) + BitVec.ofNat 64 d)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 so) n) t := by
  set A := State.addr (s.gpr src) + BitVec.ofNat 64 so
  set B := State.addr (s.gpr dst) + BitVec.ofNat 64 d
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ =>
    WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Stream.Arm.CopyInv s A B n 0 s₁ :=
    ⟨by rw [u₁.rd, u₀.rd], by rw [u₁.wr, u₀.wr], by rw [u₁.sp, u₀.sp],
      fun r hr => by rw [u₁.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r9), u₀.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r8)],
      by rw [u₁.other _ (by decide), u₀.gpr]; rfl, by rw [u₁.gpr, VG.Proof.Pbkdf2.Stream.Arm.movw_ofNat hn']; rfl,
      by rw [u₁.mem, u₀.mem, bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Stream.Arm.count_loop hn (VG.Proof.Pbkdf2.Stream.Arm.CopyInv s A B n) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) hso
    (by rw [u₁.gpr, h.other src hs, h.r8, VG.Proof.Pbkdf2.Stream.Arm.addr3 (by omega_nat)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (VG.Proof.Pbkdf2.Stream.Arm.nm hd .r12), u₁.other dst (VG.Proof.Pbkdf2.Stream.Arm.nm hd .r2), h.other dst hd,
      u₂.other .r8 (by decide), u₁.other .r8 (by decide), h.r8, VG.Proof.Pbkdf2.Stream.Arm.addr3 (by omega_nat)])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ =>
    WP.block_nil ?_
  have h8 : t₅.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8,
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32]
  have h9 : t₅.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r9), u₅.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r8), m₄.gpr, u₃.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r2), u₂.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r12),
        u₁.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r2), h.other r hr],
    by rw [u₆.other _ (by decide), h8], by rw [u₆.gpr, h9, VG.Proof.Pbkdf2.Stream.Arm.left_val hk], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₃.gpr .r12).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
      simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
      ext i hi; simp
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_nat)
    rw [hl] at e'
    rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [z₆, h9, VG.Proof.Pbkdf2.Stream.Arm.left_z hk (by omega_nat)]

/-! ## The exclusive-or of `U` into `T` -/

theorem xor_byte32 (a b : Byte) : ((b.setWidth 32 ^^^ a.setWidth 32).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ VG.Proof.Pbkdf2.Stream.Arm.clob, t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 32 k
  r9 : t.gpr .r9 = BitVec.ofNat 32 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `r11 + uo` and `T` at `r5`. -/
theorem xor_ok {uo n : Nat} (huo : uo < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (huw : (s.gpr .r11).toNat + uo + n ≤ 2 ^ 32) (htw : (s.gpr .r5).toNat + n ≤ 2 ^ 32)
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r11) + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr (State.addr (s.gpr .r5) + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r11) + BitVec.ofNat 64 uo, n⟩ ⟨State.addr (s.gpr .r5), n⟩) :
    WP isa (.seq (.block [.mov .r8 (.imm 0), .movw .r9 (BitVec.ofNat 16 n)])
      (.loop (.block [.dp .add .r2 .r11 (.reg .r8), .ldrb .r12 .r2 uo, .dp .add .r2 .r5 (.reg .r8),
        .ldrb .r1 .r2 0, .dp .eor .r1 .r1 (.reg .r12), .strb .r1 .r2 0, .dp .add .r8 .r8 (.imm 1),
        .subs .r9 .r9 (.imm 1)]) .ne)) s
      fun t => VG.Proof.Pbkdf2.Stream.Arm.XorInv s (State.addr (s.gpr .r11) + BitVec.ofNat 64 uo) (State.addr (s.gpr .r5)) n n t := by
  set U := State.addr (s.gpr .r11) + BitVec.ofNat 64 uo
  set T := State.addr (s.gpr .r5)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ =>
    WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Stream.Arm.XorInv s U T n 0 s₁ :=
    ⟨by rw [u₁.rd, u₀.rd], by rw [u₁.wr, u₀.wr], by rw [u₁.sp, u₀.sp],
      fun r hr => by rw [u₁.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r9), u₀.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r8)],
      by rw [u₁.other _ (by decide), u₀.gpr]; rfl, by rw [u₁.gpr, VG.Proof.Pbkdf2.Stream.Arm.movw_ofNat hn']; rfl,
      by rw [u₁.mem, u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, VG.WriteBytes.writeBytes_nil]⟩
  refine VG.Proof.Pbkdf2.Stream.Arm.count_loop hn (VG.Proof.Pbkdf2.Stream.Arm.XorInv s U T n) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [VG.WriteBytes.writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [VG.WriteBytes.writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by rw [BitVec.add_comm, BitVec.add_sub_cancel],
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_nat), Nat.lt_irrefl, ↓reduceIte]
  have g11 := h.other .r11 (by decide)
  have g5 := h.other .r5 (by decide)
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := U + BitVec.ofNat 64 k) huo (by rw [u₁.gpr, g11, h.r8, VG.Proof.Pbkdf2.Stream.Arm.addr3 (by omega_nat)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  have a₃ : State.addr (t₃.gpr .r2 + BitVec.ofNat 32 0) = T + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g5, h.r8, VG.Proof.Pbkdf2.Stream.Arm.addr3 (by omega_nat)]
    exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _)
  refine wp_ldrb (a := T + BitVec.ofNat 64 k) (by decide) a₃
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact InRegions.right' (houtT k hk))
    fun t₄ u₄ => ?_
  refine VG.Proof.Pbkdf2.Stream.Arm.wp_eor (op2_reg _ _) fun t₅ u₅ => ?_
  refine wp_strb (a := T + BitVec.ofNat 64 k) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact houtT k hk) fun t₆ m₆ => ?_
  refine wp_add (op2_imm (by decide)) fun t₇ u₇ => wp_subs (op2_imm (by decide)) fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have h8 : t₇.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r8, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32]
  have h9 : t₇.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, m₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₈.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r9), u₇.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r8), m₆.gpr, u₅.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r1), u₄.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r1),
        u₃.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r2), u₂.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r12), u₁.other r (VG.Proof.Pbkdf2.Stream.Arm.nm hr .r2), h.other r hr],
    by rw [u₈.other _ (by decide), h8], by rw [u₈.gpr, h9, VG.Proof.Pbkdf2.Stream.Arm.left_val hk], ?_⟩, ?_⟩
  · have hv : (t₅.gpr .r1).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
      rw [u₅.gpr, u₄.gpr, u₄.other .r12 (by decide), u₃.other .r12 (by decide), u₂.gpr, u₃.mem, u₂.mem,
        u₁.mem, VG.Proof.Pbkdf2.Stream.Arm.xor_byte32, rU, rT]
    have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega_nat)
    rw [hl'] at e'
    rw [u₈.mem, u₇.mem, m₆.mem, hv, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem, e',
      bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [z₈, h9, VG.Proof.Pbkdf2.Stream.Arm.left_z hk (by omega_nat)]

end VG.Proof.Pbkdf2.Stream.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: our caller's registers

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`): the callee-saved
registers we use, and our return address `lr`, are stored in `scratch` after
the working space of the functions we call (`Hash.saved`), with `scratch` in
`r12`, and loaded back at the end, with `scratch` in `r11`, which is loaded
last.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd wp_ldr saveMem saveList_ok readW_writeW_save sub_offset)
open VG.Proof.Hmac.Generic.Common (InRegions.right' add_ofNat_add)

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr, .r11]

theorem preserved_saved : ∀ r ∈ preserved, r ∈ VG.Proof.Pbkdf2.Stream.Arm.savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨State.addr scr + BitVec.ofNat 64 (8 * H.W), 36⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 36 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_nat

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 36) :
    Region.Sub ⟨State.addr scr + BitVec.ofNat 64 d, 4⟩ (VG.Proof.Pbkdf2.Stream.Arm.saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega_nat, ← add_ofNat_add]
  exact VG.Proof.MdStream.Arm.sub_offset (by omega_nat) (by omega_nat)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Stream.Arm.saveR H scr).Disjoint r) :
    VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.Arm.saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Stream.Arm.slot_sub H scr h₁ h₂)) (by decide)

theorem saveMem_other (m : Mem) (B : Addr) (g : Reg → BitVec 32) {d : Nat} (hd : d < 2 ^ 32) :
    ∀ l : List (Reg × Nat), (∀ q ∈ l, q.2 < 2 ^ 32 ∧ (d + 4 ≤ q.2 ∨ q.2 + 4 ≤ d)) →
    (VG.Arm.Spill.saveMem m B g l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | [], _ => rfl
  | q :: l, h => by
    rw [VG.Arm.Spill.saveMem, VG.Proof.Pbkdf2.Stream.Arm.saveMem_other _ B g hd l fun q' hq' => h q' (List.mem_cons_of_mem _ hq'),
      readW_writeW_save _ _ _ hd (h q (by simp)).1 (h q (by simp)).2]

theorem saveMem_read (B : Addr) (g : Reg → BitVec 32) :
    ∀ (m : Mem) (l : List (Reg × Nat)), l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    (∀ p ∈ l, p.2 < 2 ^ 32) → ∀ p ∈ l, (VG.Arm.Spill.saveMem m B g l).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1
  | _, [], _, _, p, hp => by cases hp
  | m, q :: l, hpw, hb, p, hp => by
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [VG.Arm.Spill.saveMem, VG.Proof.Pbkdf2.Stream.Arm.saveMem_other _ _ _ (hb p (by simp)) l
        (fun q' hq' => ⟨hb q' (List.mem_cons_of_mem _ hq'), hpw.1 q' hq'⟩), Mem.readW_writeW_self32]
    · rw [VG.Arm.Spill.saveMem]
      exact VG.Proof.Pbkdf2.Stream.Arm.saveMem_read B g _ l hpw.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq')) p hp

theorem saveMem_frameR (B : Addr) (g : Reg → BitVec 32) (o L : Nat) (hL : o + L < 2 ^ 64) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, o ≤ p.2 ∧ p.2 + 4 ≤ o + L) →
    Frame [⟨B + BitVec.ofNat 64 o, L⟩] m (VG.Arm.Spill.saveMem m B g l)
  | _, [], _ => Frame.refl _ _
  | m, p :: l, hl => by
    obtain ⟨h₁, h₂⟩ := hl p (by simp)
    have c : (⟨B + BitVec.ofNat 64 o, L⟩ : Region).Contains (B + BitVec.ofNat 64 p.2) (32 / 8) := by
      rw [show p.2 = o + (p.2 - o) by omega_nat, ← add_ofNat_add]
      exact VG.Proof.MdStream.Arm.contains_offset (by omega_nat) (by omega_nat)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c).trans
      (VG.Proof.Pbkdf2.Stream.Arm.saveMem_frameR B g o L hL _ l fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem save_eq : H.save = H.saved.map (fun p => Instr.str p.1 .r12 p.2) := rfl

/-- Saving the registers, with `scratch` in `r12`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (h12 : s.gpr .r12 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [VG.Proof.Pbkdf2.Stream.Arm.saveR H scr] s.mem s'.mem → VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [VG.Proof.Pbkdf2.Stream.Arm.save_eq]
  refine VG.Arm.Spill.saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · obtain ⟨h₁, h₂⟩ := VG.Proof.Pbkdf2.Stream.Arm.saved_mem H hp
    rw [h12]
    exact ⟨by omega_nat, by omega_nat, ⟨_, hsc, VG.Proof.MdStream.Arm.contains_offset (by omega_nat) (by omega_nat)⟩⟩
  · rw [m, h12]
    exact VG.Proof.Pbkdf2.Stream.Arm.saveMem_frameR _ _ _ _ (by omega_nat) _ _ fun p hp => VG.Proof.Pbkdf2.Stream.Arm.saved_mem H hp
  · intro p hp
    rw [m, h12]
    exact VG.Proof.Pbkdf2.Stream.Arm.saveMem_read _ _ _ _ (VG.Proof.Pbkdf2.Stream.Arm.saved_pairwise H) (fun q hq => by have := VG.Proof.Pbkdf2.Stream.Arm.saved_mem H hq; omega_nat) p hp

theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

/-- The slots loaded before `r11`. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 8 * H.W), (.r5, 8 * H.W + 4), (.r6, 8 * H.W + 8), (.r7, 8 * H.W + 12), (.r8, 8 * H.W + 16),
    (.r9, 8 * H.W + 20), (.r10, 8 * H.W + 24), (.lr, 8 * H.W + 28)]

theorem restore_eq :
    H.restore = (VG.Proof.Pbkdf2.Stream.Arm.saved8 H).map (fun p => Instr.ldr p.1 .r11 p.2) ++ ([.ldr .r11 .r11 (8 * H.W + 32)] : List Instr) := rfl

theorem saved8_fst : (VG.Proof.Pbkdf2.Stream.Arm.saved8 H).map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr] := rfl

theorem saved8_sub {p : Reg × Nat} (hp : p ∈ VG.Proof.Pbkdf2.Stream.Arm.saved8 H) : p ∈ H.saved := by
  simp only [VG.Proof.Pbkdf2.Stream.Arm.saved8, Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with h | h | h | h | h | h | h | h <;> simp [h]

/-- Loading them back, with `scratch` in `r11` (loaded last). -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (h11 : s.gpr .r11 = scr) (hW : H.W ≤ 64)
    {s₀ : State} (hs : VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s₀ s.mem) (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.Pbkdf2.Stream.Arm.savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Pbkdf2.Stream.Arm.savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {d}, d + 4 ≤ L →
      InRegions (t.rd ++ t.wr) (State.addr scr + BitVec.ofNat 64 d) 4 := fun hr hw d hd => by
    rw [hr, hw]; exact InRegions.right' ⟨_, hsc, VG.Proof.MdStream.Arm.contains_offset hd (by omega_nat)⟩
  rw [VG.Proof.Pbkdf2.Stream.Arm.restore_eq]
  refine VG.Proof.Pbkdf2.Stream.Arm.restoreList_ok (VG.Proof.Pbkdf2.Stream.Arm.saved8 H) s _ (by rw [VG.Proof.Pbkdf2.Stream.Arm.saved8_fst]; decide) (fun p hp => ?_)
    fun s₁ hl ho hm hrd hwr hsp => ?_
  · have := VG.Proof.Pbkdf2.Stream.Arm.saved_mem H (VG.Proof.Pbkdf2.Stream.Arm.saved8_sub H hp)
    refine ⟨?_, by omega_nat, by rw [h11]; omega_nat, by rw [h11]; exact io rfl rfl (by omega_nat)⟩
    simp only [VG.Proof.Pbkdf2.Stream.Arm.saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have e11 : s₁.gpr .r11 = scr := by
    rw [ho _ (by rw [VG.Proof.Pbkdf2.Stream.Arm.saved8_fst]; decide), h11]
  refine wp_ldr (by omega_nat) (addr_add (by rw [e11]; omega_nat)) (by rw [e11]; exact io hrd hwr (by omega_nat))
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, hm], by rw [u.rd, hrd], by rw [u.wr, hwr], by rw [u.sp, hsp],
      fun r hr => ?_, fun r hr => ?_⟩
  · have hv : ∀ p ∈ VG.Proof.Pbkdf2.Stream.Arm.saved8 H, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      have h1 : p.1 ≠ .r11 := by
        simp only [VG.Proof.Pbkdf2.Stream.Arm.saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
      rw [u.other _ h1, hl p hp, h11, hs p (VG.Proof.Pbkdf2.Stream.Arm.saved8_sub H hp)]
    simp only [VG.Proof.Pbkdf2.Stream.Arm.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv (.r4, 8 * H.W) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r5, 8 * H.W + 4) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r6, 8 * H.W + 8) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r7, 8 * H.W + 12) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r8, 8 * H.W + 16) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r9, 8 * H.W + 20) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.r10, 8 * H.W + 24) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · exact hv (.lr, 8 * H.W + 28) (by simp [VG.Proof.Pbkdf2.Stream.Arm.saved8])
    · rw [u.gpr, e11, hm, hs (.r11, 8 * H.W + 32) (by simp [Hash.saved])]
  · simp only [VG.Proof.Pbkdf2.Stream.Arm.savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other r hr.2.2.2.2.2.2.2.2, ho r (by
      rw [VG.Proof.Pbkdf2.Stream.Arm.saved8_fst]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1⟩)]

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s₁ m)
    (he : ∀ r ∈ VG.Proof.Pbkdf2.Stream.Arm.savedRegs, s₁.gpr r = s₀.gpr r) : VG.Proof.Pbkdf2.Stream.Arm.SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Odds and ends -/

theorem below_eq {s t : State} (h : s.sp = t.sp) : VG.Proof.Pbkdf2.Stream.Arm.below s = VG.Proof.Pbkdf2.Stream.Arm.below t := by simp only [VG.Proof.Pbkdf2.Stream.Arm.below, h]

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_nat)

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

/-- A streaming state is kept by what writes elsewhere. -/
theorem repr_keep {H : Hash} (hH : VG.Proof.Pbkdf2.Stream.Arm.HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

end VG.Proof.Pbkdf2.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes`. -/
section

/-!
# HMAC over any streaming hash function on 32-bit ARM: the hash functions

`HashOK` for SHA-1, MD5 and the SHA-512 family, from their own proofs, as on
x86 (`Proof/Pbkdf2/Stream/X86/Hashes.lean`). Their contracts are `initK`,
`updK` and `finK` at their sizes, but for the length bound of SHA-1's and
MD5's `finK`, and for the SHA-512 family's, which hold from any initial hash
value. SHA-256's and SHA-224's are in `Sha256.lean` and `Sha224.lean`.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Hmac.Generic.Common (sha1_repr md5_repr sha512_repr finalHash_length)

/-! ## SHA-1 -/

def sha1H : Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init", Impl.Sha1.Arm.Stream.init,
  "vg_sha1_update_scratch", Impl.Sha1.Arm.Stream.update, "vg_sha1_finalize_scratch", Impl.Sha1.Arm.Stream.finalize⟩

def sha1OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha1H where
  SH := Spec.Hmac.sha1S
  Wb := 160
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
  repr := sha1_repr
  init := Proof.Sha1.Arm.Stream.init_verified
  upd := Proof.Sha1.Arm.Stream.Update.update_verified
  fin := Proof.Sha1.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha1.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

/-! ## MD5 -/

def md5H : Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.Arm.Stream.init,
  "vg_md5_update_scratch", Impl.Md5.Arm.Stream.update, "vg_md5_finalize_scratch", Impl.Md5.Arm.Stream.finalize⟩

def md5OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.md5H where
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
  init := Proof.Md5.Arm.Stream.init_verified
  upd := Proof.Md5.Arm.Stream.Update.update_verified
  fin := Proof.Md5.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.Arm.Stream.init iv, "vg_sha512_update_scratch",
    Impl.Sha512.Arm.Stream.update, "vg_sha512_finalize_scratch", Impl.Sha512.Arm.Stream.finalize⟩

theorem sha512_updNF : Impl.Sha512.Arm.Stream.update.noFrames = true := by decide +kernel
theorem sha512_finNF : Impl.Sha512.Arm.Stream.finalize.noFrames = true := by decide +kernel

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hINF : (Impl.Sha512.Arm.Stream.init iv).noFrames = true) :
    VG.Proof.Pbkdf2.Stream.Arm.HashOK (VG.Proof.Pbkdf2.Stream.Arm.sha512H D initN iv) where
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
  init := hR ▸ Proof.Sha512.Arm.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha512.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := hINF
  updNF := VG.Proof.Pbkdf2.Stream.Arm.sha512_updNF
  finNF := VG.Proof.Pbkdf2.Stream.Arm.sha512_finNF

def sha384H : Hash := VG.Proof.Pbkdf2.Stream.Arm.sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : Hash := VG.Proof.Pbkdf2.Stream.Arm.sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : Hash := VG.Proof.Pbkdf2.Stream.Arm.sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : Hash := VG.Proof.Pbkdf2.Stream.Arm.sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha384H := VG.Proof.Pbkdf2.Stream.Arm.sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha512H' := VG.Proof.Pbkdf2.Stream.Arm.sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm) (by decide) (by decide)
  (by decide +kernel)
def sha512_224OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha512_224H := VG.Proof.Pbkdf2.Stream.Arm.sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512_256OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha512_256H := VG.Proof.Pbkdf2.Stream.Arm.sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)

end VG.Proof.Pbkdf2.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha224`. -/
section

/-!
# SHA-224's streaming functions on 32-bit ARM

`HashOK` for SHA-224 (`sha224OK`): SHA-256's streaming functions from
SHA-224's initial hash value (`vg_sha224_init`, then `vg_sha256_update` and
`vg_sha256_finalize`, whose contracts hold from any initial hash value), with
the digest the first 28 bytes of the final hash value.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Hmac.Generic.Common (readW_reloc bytesAt_reloc)

/-- SHA-224's functions: SHA-256's streaming state, 96 bytes, and working
space, 20 words; a 28-byte digest, of the 32 bytes `finalize` writes. -/
def sha224H : Hash := ⟨64, 96, 28, 32, 20, "vg_sha224_init", Impl.Sha256.Arm.Stream.init224,
  "vg_sha256_update_scratch", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize_scratch", Impl.Sha256.Arm.Stream.finalize⟩

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

def sha224OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha224H where
  SH := Spec.Hmac.sha224S
  Wb := 160
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
  repr := VG.Proof.Pbkdf2.Stream.Arm.sha224_repr
  init := Proof.Sha256.Arm.Stream.init224_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

end VG.Proof.Pbkdf2.Stream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256`. -/
section

/-!
# SHA-256's streaming functions on 32-bit ARM

`HashOK` for SHA-256 (`sha256OK`): its streaming functions
(`vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize`, whose
contracts for `update` and `finalize` hold from any initial hash value).
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)

/-- SHA-256's functions: a 96-byte streaming state, 20 words of working
space and a 32-byte digest. -/
def sha256H : Hash := ⟨64, 96, 32, 32, 20, "vg_sha256_init", Impl.Sha256.Arm.Stream.init,
  "vg_sha256_update_scratch", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize_scratch", Impl.Sha256.Arm.Stream.finalize⟩

def sha256OK : VG.Proof.Pbkdf2.Stream.Arm.HashOK VG.Proof.Pbkdf2.Stream.Arm.sha256H where
  SH := Spec.Hmac.sha256S
  Wb := 160
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
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.Arm.Stream.init_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

end VG.Proof.Pbkdf2.Stream.Arm

end
