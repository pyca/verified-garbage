module

public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

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

@[expose] public section

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
  post s s' := ∀ m, R s.mem (State.addr (s.gpr .r0)) m → count s = BitVec.ofNat 64 m.length →
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
    count s = BitVec.ofNat 64 m.length → (bytesAt s'.mem (State.addr (stackArg s 0)) F).take D = hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `Proof.Hmac.initScratchContract`. -/
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
    (below s).Disjoint inner ∧ (below s).Disjoint outer ∧ (below s).Disjoint key ∧
    (below s).Disjoint scratch ∧
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

/-- `finalize(inner, outer, count, out, scratch)`: `Proof.Hmac.finalizeScratchContract`. -/
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
    (below s).Disjoint inner ∧ (below s).Disjoint outer ∧ (below s).Disjoint out ∧
    (below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + S.digestBytes ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad ++ text) →
    count s = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (State.addr (s.gpr .r1)) (xorPad k0 opad) →
    bytesAt s'.mem (State.addr (stackArg s 0)) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `iterate(key, u, n, t, scratch)`: `Proof.Pbkdf2.iterateContract`. -/
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
    (below s).Disjoint key ∧ (below s).Disjoint u ∧ (below s).Disjoint t ∧ (below s).Disjoint scratch ∧
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
in `r2:r3`: `fin_frame` runs such a frame, from the state before its push.
A frame writes the 16 bytes below the stack pointer, which `After` lets
change. `init_rel` and `fin_rel` relate two runs of `init` and `finalize`
(`RelCT.call`, `RelCT.frame`).
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
  init : Verified Arm.target H.initC (initK H.S SH.Repr)
  upd : Verified Arm.target H.updC (updK H.S Wb SH.Repr)
  fin : Verified Arm.target H.finC (finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initNF : H.initC.noFrames = true
  updNF : H.updC.noFrames = true
  finNF : H.finC.noFrames = true

variable {H : Hash} (hH : HashOK H)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s]) s.mem s'.mem

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
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩] s' → hH.SH.Repr s'.mem (State.addr st) [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.callCalls (k := initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨State.addr st, H.S⟩]) ?_
    (covers_wr hc) hc ?_ hH.initNF
  · exact ⟨rfl, by simp [h0], by simpa [h0] using hn⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ _ hpost
    refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_app h₄⟩ ?_
    simpa [initK, h0] using hpost

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
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using addr_sub_add hk (Nat.zero_le k)

/-- Bytes at two offsets from a base that do not overlap. -/
theorem sep_off (b : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32)
    (he : e + k < 2 ^ 32) : Mem.Sep (b + BitVec.ofNat 64 d) n (b + BitVec.ofNat 64 e) k := Offset.sep b h (by omega_nat) (by omega_nat)

/-- Bytes at a base and at an offset from it that do not overlap. -/
theorem sep_base_off (b : Addr) {e n k : Nat} (h : n ≤ e) (he : e + k < 2 ^ 32) :
    Mem.Sep b n (b + BitVec.ofNat 64 e) k := Offset.sep_base b h (by omega_nat)

/-- Bytes at an offset from a region's base, in it. -/
theorem contains_off (b : Addr) {len d n : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 64) :
    Region.Contains ⟨b, len⟩ (b + BitVec.ofNat 64 d) n := Offset.contains_base b h (by omega_nat)

/-- After a frame of `rs` of `n` bytes around a call that keeps the regions
and the stack pointer. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem) (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    After s ws (popped .r1 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr1 : r ≠ .r1 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr1, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (frame_app (ws' := [below s]) hf)

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
  b_st : (below s).Disjoint ⟨State.addr st, H.S⟩
  b_o : (below s).Disjoint ⟨State.addr o, H.F⟩
  b_sc : (below s).Disjoint ⟨State.addr sc, hH.Wb⟩
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
variable {hH} {s : State} {st o sc : BitVec 32} (h : FinArgs hH s st o sc)
include h

theorem a8 : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub (k := 8) (by have := h.sp16; omega_nat)
theorem a4 : State.addr (s.sp - 8 + 4) = State.addr s.sp - 8 + BitVec.ofNat 64 4 :=
  addr_sub_add (k := 8) (i := 4) (by have := h.sp16; omega_nat) (by decide)

theorem pmem : (pushed fin2 s).mem =
    (s.mem.writeW (State.addr s.sp - 8) o).writeW (State.addr s.sp - 8 + BitVec.ofNat 64 4) sc := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * fin2.length)) [s.gpr .r1, s.gpr .r12] = _
  rw [e8]
  show (s.mem.writeW (State.addr (s.sp - 8)) _).writeW (State.addr (s.sp - 8 + 4)) _ = _
  rw [h.a8, h.a4, h.r1, h.r12]

omit h in
theorem psp : (pushed fin2 s).sp = s.sp - 8 := by rw [pushed_sp, e8]

theorem sa0 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 0 = State.addr s.sp - 8 := by
  simp only [stackArgAddr, ht]
  rw [BitVec.add_zero]; exact h.a8

theorem sa1 (T : State) (ht : T.sp = s.sp - 8) : stackArgAddr T 1 = State.addr s.sp - 8 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr, ht]; exact h.a4

theorem arg0 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed fin2 s).mem) : stackArg T 0 = o := by
  rw [stackArg, h.sa0 T ht, hm, h.pmem, Mem.readW_writeW_sep (sep_base_off _ (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 8) (hm : T.mem = (pushed fin2 s).mem) : stackArg T 1 = sc := by
  rw [stackArg, h.sa1 T ht, hm, h.pmem, Mem.readW_writeW_self32]

theorem fP : Frame [below s] s.mem (pushed fin2 s).mem := by
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
theorem vsp : ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)).sp = s.sp - 8 := psp
omit h in
theorem vmem : ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)).mem = (pushed fin2 s).mem := rfl

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 8, 8⟩ (below s) :=
  Offset.sub_below _ (a := 8) (b := 16) (by omega_nat) (by omega_nat)

theorem pre : (finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
    ((pushed fin2 s).callEntry.withRegions (rd s.sp) (wr hH st o sc)) := by
  simp only [finK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, pushed_gpr,
    h.arg0 _ vsp vmem, h.arg1 _ vsp vmem, h.sa0 _ vsp, h.r0]
  refine ⟨trivial, trivial, h.st_o, h.st_sc, h.o_sc, (h.b_st.sub_left argsSub), (h.b_o.sub_left argsSub),
    (h.b_sc.sub_left argsSub), h.nst, h.no, h.nsc, ?_⟩
  rw [vsp, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (rd s.sp ++ wr hH st o sc) ((pushed fin2 s).rd ++ (pushed fin2 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e8]
  rcases hr with rfl | (rfl | rfl | rfl)
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a8]; simp only [Region.Contains, fin2, List.length_cons, List.length_nil] at hcn ⊢; omega_nat
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr hH st o sc) (pushed fin2 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end FinArgs

theorem fin_frame {s : State} {st o sc : BitVec 32} (h : FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, H.S⟩, ⟨State.addr o, H.F⟩, ⟨State.addr sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem (State.addr st) m → m.length < 2 ^ 64 → count s = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (State.addr o) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := fin2) (r := .r1) rfl (by show 8 ≤ s.sp.toNat; omega_nat) (by decide) ?_
  refine WP.callCalls (k := finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 h.pre h.cov h.covW ?_ hH.finNF
  intro s₂ hrd hwr hsp hf hcs _ hpost
  have vc : count ((pushed fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)) = count s := by
    simp only [count, State.withRegions_gpr, ce2, ce3, pushed_gpr]
  simp only [finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, pushed_gpr, h.r0,
    h.arg0 _ FinArgs.vsp FinArgs.vmem, vc] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hf hcs) fun m hr hl hcm => ?_
  have hs : ∀ r ∈ [below s], (⟨State.addr st, H.S⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact h.b_st.symm
  have hr' : hH.SH.Repr (pushed fin2 s).mem (State.addr st) m :=
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
    covers_wr c, c, covers_wr c', c'⟩
  simp only [initK, State.withRegions_gpr, ce0, d, d']

theorem fin_rel {P : State → State → Prop} {sp : BitVec 32} {st o sc : BitVec 32}
    (h : ∀ s s', P s s' → FinArgs hH s st o sc ∧ FinArgs hH s' st o sc ∧ count s = count s' ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hH.fin.1 hH.fin.2.1 (FinArgs.rd sp) (FinArgs.wr hH st o sc)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨f, f', hc, e, e'⟩ := h s s' hp
  rw [push_eq rfl pa, push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : FinArgs.rd s.sp = FinArgs.rd s'.sp := by rw [v]
  have t1 : ((pushed fin2 s).callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s.sp - 8 := FinArgs.psp
  have t2 : ((pushed fin2 s').callEntry.withRegions (FinArgs.rd s.sp) (FinArgs.wr hH st o sc)).sp =
    s'.sp - 8 := FinArgs.psp
  refine ⟨f.pre, hv' ▸ f'.pre, ?_, f.cov, f.covW, hv' ▸ f'.cov, f'.covW⟩
  obtain ⟨c3, c2⟩ := BitVec.append_32_inj hc
  simp only [finK]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, ce0, pushed_gpr, f.r0, f'.r0]
  · simp only [State.withRegions_gpr, ce2, pushed_gpr, c2]
  · simp only [State.withRegions_gpr, ce3, pushed_gpr, c3]
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

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Pbkdf2.Stream.Arm
