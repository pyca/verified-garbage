import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the calls

The contracts the proofs are written against, as on x86-64
(`Proof/Pbkdf2/Md/X86_64/Calls.lean`).

* `initK`, `updK` and `finK` are the AArch64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. Each lets the callee
  use the 16 bytes below the stack pointer (a frame saving `x30`), as SHA-1's
  and MD5's do; the contracts the functions are proved against imply them
  (the SHA-512 family's, which use no stack, too).
* `initG` and `finG` are those of HMAC's `init` and `finalize`, which use no
  stack of their own but let the functions they call use those 16 bytes;
  the artifacts are emitted with the shared contracts of
  `Spec/Hmac/Generic.lean`, which imply them (`initImp`, `finImp`,
  `Contract.lean`).

The return address is in `x30`, not on the stack, so no region needs to be
kept disjoint from it.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- The 16 bytes below the stack pointer. -/
abbrev stk (s : State) : Region := ⟨s.sp - 16, 16⟩

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, S⟩]
  post s s' := R s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, Wb⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint state ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint data ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, S⟩
    let out : Region := ⟨s.gpr .x2, F⟩
    let scratch : Region := ⟨s.gpr .x3, Wb⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint state ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint out ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .x2) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-! ## Our functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initScratchContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    (s.gpr .x3).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint inner ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint outer ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint key ∧
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    S.Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeScratchContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let out : Region := ⟨s.gpr .x3, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint inner ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint outer ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint out ∧
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .x0) (xorPad k0 ipad ++ text) →
    s.gpr .x2 = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .x1) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .x3) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# The streaming functions, called

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Calls.lean`): `StreamOK H` is what the
proofs know of the streaming functions `H` of a hash function: they are
verified against `initK`, `updK` and `finK`, the representation of the
streaming state is determined by the state's bytes, and the sizes are small. From it, each
call is run with `WP.callFV` (the callee may have a frame, in the 16 bytes
below the stack pointer), and shown constant time in two runs with
`RelCT.call`. A call writes no memory of its own on AArch64: the return
address is in `x30`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's AArch64 functions, verified. `Wb` is the
scratch space their contracts use, at most the `8 W` bytes we give them. -/
structure StreamOK (H : Stream) where
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
  hW : H.W ≤ 134
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified AArch64.target H.initC (VG.Proof.Pbkdf2.Md.AArch64.Calls.initK H.S SH.Repr)
  upd : Verified AArch64.target H.updC (VG.Proof.Pbkdf2.Md.AArch64.Calls.updK H.S Wb SH.Repr)
  fin : Verified AArch64.target H.finC (VG.Proof.Pbkdf2.Md.AArch64.Calls.finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initDepth : H.initC.aarch64Depth ≤ 1
  updDepth : H.updC.aarch64Depth ≤ 1
  finDepth : H.finC.aarch64Depth ≤ 1

variable {H : Stream} (hH : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK H)

theorem stk_eq (s : State) : VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s = below s.sp 16 := rfl

/-- The ABI-preserved low halves of v8–v15. -/
abbrev VecKept (s s' : State) : Prop :=
  ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem VecKept.trans {s t u : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.VecKept s t) (k : VG.Proof.Pbkdf2.Md.AArch64.Calls.VecKept t u) : VG.Proof.Pbkdf2.Md.AArch64.Calls.VecKept s u :=
  fun r hr => (k r hr).trans (h r hr)

/-- What a call leaves: the regions, stack pointer, callee-saved GPRs except
`x30`, preserved SIMD low halves, memory outside its writable regions, and
the addresses of statics. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s.sp 16]) s.mem s'.mem
  vec : VG.Proof.Pbkdf2.Md.AArch64.Calls.VecKept s s'
  syms : s'.syms = s.syms

/-- The stack of a callee with at most one frame. -/
theorem frame_depth {c : Prog isa} (hd : c.aarch64Depth ≤ 1) {s : State} {ws : List Region} {m' : Mem}
    (h : Frame (ws ++ [below s.sp (16 * c.aarch64Depth)]) s.mem m') :
    Frame (ws ++ [below s.sp 16]) s.mem m' :=
  Frame.below_mono h (by omega_nat) (by omega_nat)

theorem fdepth_lt {c : Prog isa} (hd : c.aarch64Depth ≤ 1) : 16 * c.aarch64Depth < 2 ^ 64 := by omega_nat

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := State.callEntry_gpr s (by decide)
@[simp] theorem ce3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := State.callEntry_gpr s (by decide)
@[simp] theorem ce4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := State.callEntry_gpr s (by decide)

/-! ## `init` -/

theorem init_call {s : State} {st : Addr} (h0 : s.gpr .x0 = st) (hc : Covers [⟨st, H.S⟩] s.wr)
    {Q : State → Prop} (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨st, H.S⟩] s' → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.of_syms (WP.callFV (k := VG.Proof.Pbkdf2.Md.AArch64.Calls.initK H.S hH.SH.Repr) hH.init.1 (rd := []) (wr := [⟨st, H.S⟩]) ?_
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr hc) hc ?_ (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hH.initDepth))
  · exact ⟨rfl, by simp [VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, h0]⟩
  · intro s' h₁ h₂ h₃ h₄ h₅ hv hpost hsy
    refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hH.initDepth h₄, hv, hsy⟩ ?_
    simpa [VG.Proof.Pbkdf2.Md.AArch64.Calls.initK, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4, h0] using hpost

/-! ## `update` -/

/-- The regions of a call of `update`. -/
structure UpdArgs (s : State) (st d sc : Addr) (len : Nat) : Prop where
  x0 : s.gpr .x0 = st
  x2 : s.gpr .x2 = d
  x3 : (s.gpr .x3).toNat = len
  x4 : s.gpr .x4 = sc
  cd : Covers [⟨d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, H.S⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, hH.Wb⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_st : (below s.sp 16).Disjoint ⟨st, H.S⟩
  stk_d : (below s.sp 16).Disjoint ⟨d, len⟩
  stk_sc : (below s.sp 16).Disjoint ⟨sc, hH.Wb⟩

theorem UpdArgs.covers {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs hH s st d sc len) :
    Covers ([⟨d, len⟩] ++ [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) (s.rd ++ s.wr) :=
  fun a n hi => by
    rcases List.mem_append.mp (show _ ∈ _ from hi.choose_spec.1) with hr | hr
    · exact h.cd a n ⟨_, hr, hi.choose_spec.2⟩
    · obtain ⟨r, hr', hc⟩ := h.cw a n ⟨_, hr, hi.choose_spec.2⟩
      exact ⟨r, List.mem_append_right _ hr', hc⟩

theorem UpdArgs.pre {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs hH s st d sc len) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.updK H.S hH.Wb hH.SH.Repr).pre (s.callEntry.withRegions [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4, h.x0, h.x2, h.x3, h.x4]
  exact ⟨by trivial, by trivial, h.st_sc, h.d_st, h.d_sc, h.sp16, h.stk_st, h.stk_d, h.stk_sc⟩

theorem upd_call {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs hH s st d sc len)
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .x1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem d len)) → Q s') :
    WP isa (.call H.updN H.updC) s Q := by
  refine WP.of_syms (WP.callFV (k := VG.Proof.Pbkdf2.Md.AArch64.Calls.updK H.S hH.Wb hH.SH.Repr) hH.upd.1 (h.pre hH) (h.covers hH) h.cw ?_
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hH.updDepth))
  intro s' h₁ h₂ h₃ h₄ h₅ hv hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hH.updDepth h₄, hv, hsy⟩ fun m hr hc => ?_
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.updK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, h.x0,
    h.x2, h.x3] at hpost
  exact hpost m hr hc

/-! ## `finalize` -/

/-- The regions of a call of `finalize`. -/
structure FinArgs (s : State) (st o sc : Addr) : Prop where
  x0 : s.gpr .x0 = st
  x2 : s.gpr .x2 = o
  x3 : s.gpr .x3 = sc
  cw : Covers [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.F⟩
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o, H.F⟩ ⟨sc, hH.Wb⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_st : (below s.sp 16).Disjoint ⟨st, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨o, H.F⟩
  stk_sc : (below s.sp 16).Disjoint ⟨sc, hH.Wb⟩

theorem FinArgs.pre {s : State} {st o sc : Addr} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH s st o sc) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
      (s.callEntry.withRegions [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, h.x0, h.x2, h.x3]
  exact ⟨by trivial, by trivial, h.st_o, h.st_sc, h.o_sc, h.sp16, h.stk_st, h.stk_o, h.stk_sc⟩

theorem fin_call {s : State} {st o sc : Addr} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem o H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) s Q := by
  refine WP.of_syms (WP.callFV (k := VG.Proof.Pbkdf2.Md.AArch64.Calls.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 (h.pre hH)
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr h.cw) h.cw ?_ (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hH.finDepth))
  intro s' h₁ h₂ h₃ h₄ h₅ hv hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hH.finDepth h₄, hv, hsy⟩ fun m hr hl hc => ?_
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, h.x0,
    h.x2] at hpost
  exact hpost m hr hl hc

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`). -/

include hH in
theorem init_rel {P : State → State → Prop} {st : Addr}
    (h : ∀ s s', P s s' → s.gpr .x0 = st ∧ s'.gpr .x0 = st ∧ Covers [⟨st, H.S⟩] s.wr ∧
      Covers [⟨st, H.S⟩] s'.wr ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', c, c', sp⟩ := h s s' hp
  refine ⟨⟨rfl, by simp [VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, d]⟩, ⟨rfl, by simp [d']⟩, ?_, VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr c, c, VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr c', c'⟩
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, d, d',
    sp]
  exact ⟨trivial, trivial⟩

theorem upd_rel {P : State → State → Prop} {st d sc : Addr} {len : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs hH s st d sc len ∧ VG.Proof.Pbkdf2.Md.AArch64.Calls.UpdArgs hH s' st d sc len ∧
      s.gpr .x1 = s'.gpr .x1 ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.updN H.updC) fun _ _ => True := by
  refine RelCT.call hH.upd.1 hH.upd.2.1 [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', x1, sp⟩ := h s s' hp
  have x3 : s.gpr .x3 = s'.gpr .x3 := BitVec.eq_of_toNat_eq (by rw [a.x3, a'.x3])
  refine ⟨a.pre hH, a'.pre hH, ?_, a.covers hH, a.cw, a'.covers hH, a'.cw⟩
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4, a.x0,
    a'.x0, a.x2, a'.x2, a.x4, a'.x4, x1, x3, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem fin_rel {P : State → State → Prop} {st o sc : Addr}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH s st o sc ∧ VG.Proof.Pbkdf2.Md.AArch64.Calls.FinArgs hH s' st o sc ∧
      s.gpr .x1 = s'.gpr .x1 ∧ s.sp = s'.sp) :
    RelCT isa P (.call H.finN H.finC) fun _ _ => True := by
  refine RelCT.call hH.fin.1 hH.fin.2.1 [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', x1, sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr a.cw, a.cw, VG.Proof.Pbkdf2.Md.AArch64.Calls.covers_wr a'.cw, a'.cw⟩
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, a.x0,
    a'.x0, a.x2, a'.x2, a.x3, a'.x3, x1, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis checks from the registers `rs` (and the stack
pointer), in two runs whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  refine ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => ?_) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨sp, hr⟩ := hag s s' h.1 h.2
  exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Pbkdf2.Md.AArch64.Calls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: what the proofs share

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Common.lean`): instructions and
arithmetic, a loop counted in `x11` (the iterations left), on which it
branches; the registers of our caller and our return address, stored in
`scratch` after the working space of the functions we call (`Stream.saved`)
and loaded back at the end; and facts about two runs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd eval_nonzero)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.MdStream.AArch64.Upd.write64 _ _ _))

end

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_nat

theorem ofNat_ne_zero {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = decide (a ≠ 0) := by
  by_cases ha : a = 0
  · subst ha; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => ha (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this)
    rw [show (BitVec.ofNat 64 a != 0) = true from bne_iff_ne.mpr this]; simp [ha]
/-- The registers the loops write. -/
abbrev clob : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

theorem nm {r : Reg} (h : r ∉ VG.Proof.Pbkdf2.Md.AArch64.Calls.clob) (x : Reg) (hx : x ∈ VG.Proof.Pbkdf2.Md.AArch64.Calls.clob := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `x11 ≠ 0` that runs its body `n > 0` times, with
`x11` the iterations left after each. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x11)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' h' => ?_
  obtain ⟨hi', hx⟩ := h'
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (n - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, hx, VG.Proof.Pbkdf2.Md.AArch64.Calls.ofNat_ne_zero (by omega_nat)]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp; omega_nat, n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩


/-- After `k` bytes of a byte copy from `A` to `B`, counted in `x24`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ VG.Proof.Pbkdf2.Md.AArch64.Calls.clob, t.gpr r = s.gpr r
  x24 : t.gpr .x24 = BitVec.ofNat 64 k
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k)

end VG.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# Our caller's registers

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Common.lean`): the six callee-saved
registers we use, and our return address `x30`, are stored in `scratch` after
the working space of the functions we call (`Stream.saved`), and loaded back
at the end, `x23` (which holds `scratch`) last.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Proof.MdStream.AArch64 (contains_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_str wp_ldr)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Stream)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x30, .x23]

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 56⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  x19 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 0) 64 = s₀.gpr .x19
  x20 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 1) 64 = s₀.gpr .x20
  x21 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 2) 64 = s₀.gpr .x21
  x22 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 3) 64 = s₀.gpr .x22
  x24 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 4) 64 = s₀.gpr .x24
  x30 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 5) 64 = s₀.gpr .x30
  x23 : m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 6) 64 = s₀.gpr .x23

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 7) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i, 8⟩ (VG.Proof.Pbkdf2.Md.AArch64.Calls.saveR H scr) := by
  rw [VG.Proof.Pbkdf2.Md.AArch64.Calls.slot, ← add_ofNat_add]
  exact Proof.MdStream.AArch64.sub_offset (by omega_nat) (by omega_nat)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 7) (hj : j < 7) (hij : i ≠ j) (hW : H.W ≤ 1024) :
    Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i, 8⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, VG.Proof.Pbkdf2.Md.AArch64.Calls.slot] at h₁ h₂
  rw [← BitVec.sub_sub] at h₁ h₂
  generalize a - scr = y at h₁ h₂
  rw [BitVec.toNat_sub, VG.Proof.MdStream.AArch64.toNat_ofNat_lt (by omega_nat)] at h₁ h₂
  have := y.isLt
  omega_nat

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : VG.Proof.Pbkdf2.Md.AArch64.Calls.SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.AArch64.Calls.saveR H scr).Disjoint r) :
    VG.Proof.Pbkdf2.Md.AArch64.Calls.SavedRegs H scr s₀ m' := by
  have k : ∀ i < 7, m'.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 64 = m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega_nat), h.x19], by rw [k 1 (by omega_nat), h.x20], by rw [k 2 (by omega_nat), h.x21],
    by rw [k 3 (by omega_nat), h.x22], by rw [k 4 (by omega_nat), h.x24], by rw [k 5 (by omega_nat), h.x30],
    by rw [k 6 (by omega_nat), h.x23]⟩

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 56 ≤ L)
    (hW : H.W ≤ 1024) {i : Nat} (hi : i < 7) : InRegions rs (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 8 :=
  ⟨_, h, VG.Proof.MdStream.AArch64.contains_offset (by omega_nat) (by omega_nat)⟩

theorem slot_eq (scr : Addr) {o : Nat} (i : Nat) (h : o = 8 * H.W + 8 * i) :
    scr + BitVec.ofNat 64 o = VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i := by rw [h]

/-- Saving the registers, with `scratch` in `x4`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h4 : s.gpr .x4 = scr) (hW : H.W ≤ 1024)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [VG.Proof.Pbkdf2.Md.AArch64.Calls.saveR H scr] s.mem s'.mem → VG.Proof.Pbkdf2.Md.AArch64.Calls.SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 7, InRegions t.wr (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact VG.Proof.Pbkdf2.Md.AArch64.Calls.slot_in H hsc hL hW hi
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x4 + BitVec.ofNat 64 o = VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i := fun hg o i h => by rw [hg, h4, h]
  simp only [Stream.save, Stream.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea rfl 0 (by omega_nat))
    (io rfl 0 (by omega_nat)) fun s₁ m₁ => ?_
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat) (ea m₁.gpr 1 (by omega_nat))
    (io m₁.wr 1 (by omega_nat)) fun s₂ m₂ => ?_
  have g₂ : s₂.gpr = s.gpr := m₂.gpr.trans m₁.gpr
  have w₂ : s₂.wr = s.wr := m₂.wr.trans m₁.wr
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat) (ea g₂ 2 (by omega_nat))
    (io w₂ 2 (by omega_nat)) fun s₃ m₃ => ?_
  have g₃ : s₃.gpr = s.gpr := m₃.gpr.trans g₂
  have w₃ : s₃.wr = s.wr := m₃.wr.trans w₂
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat) (ea g₃ 3 (by omega_nat))
    (io w₃ 3 (by omega_nat)) fun s₄ m₄ => ?_
  have g₄ : s₄.gpr = s.gpr := m₄.gpr.trans g₃
  have w₄ : s₄.wr = s.wr := m₄.wr.trans w₃
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea g₄ 4 (by omega_nat))
    (io w₄ 4 (by omega_nat)) fun s₅ m₅ => ?_
  have g₅ : s₅.gpr = s.gpr := m₅.gpr.trans g₄
  have w₅ : s₅.wr = s.wr := m₅.wr.trans w₄
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat) (ea g₅ 5 (by omega_nat))
    (io w₅ 5 (by omega_nat)) fun s₆ m₆ => ?_
  have g₆ : s₆.gpr = s.gpr := m₆.gpr.trans g₅
  have w₆ : s₆.wr = s.wr := m₆.wr.trans w₅
  refine wp_str (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat) (ea g₆ 6 (by omega_nat))
    (io w₆ 6 (by omega_nat)) fun s₇ m₇ => ?_
  refine k s₇ (m₇.gpr.trans g₆) (by rw [m₇.rd, m₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd])
    (m₇.wr.trans w₆) (by rw [m₇.sp, m₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp]) ?_ ?_
  · rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    have c : ∀ i < 7, (VG.Proof.Pbkdf2.Md.AArch64.Calls.saveR H scr).Contains (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) (64 / 8) := fun i hi => by
      rw [VG.Proof.Pbkdf2.Md.AArch64.Calls.slot, ← add_ofNat_add]; exact VG.Proof.MdStream.AArch64.contains_offset (by omega_nat) (by omega_nat)
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 3 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 6 (by omega_nat)))
  · have d : ∀ i j, i < 7 → j < 7 → i ≠ j → Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i, 8⟩ ⟨VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr j, 8⟩ :=
      fun i j hi hj hij => VG.Proof.Pbkdf2.Md.AArch64.Calls.slot_disj H scr hi hj hij hW
    rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, g₆, g₅, g₄, g₃, g₂, m₁.gpr]
    have w : ∀ i j, i < 7 → j < 7 → i ≠ j → ∀ (m : Mem) (v : BitVec 64),
        (m.writeW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr j) v).readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 64 = m.readW (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 64 :=
      fun i j hi hj hij m v => readW_writeW_ne _ _ (d i j hi hj hij)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w 0 6 (by omega_nat) (by omega_nat) (by omega_nat), w 0 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 4 (by omega_nat) (by omega_nat) (by omega_nat), w 0 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 2 (by omega_nat) (by omega_nat) (by omega_nat), w 0 1 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 1 6 (by omega_nat) (by omega_nat) (by omega_nat), w 1 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 4 (by omega_nat) (by omega_nat) (by omega_nat), w 1 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 2 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 2 6 (by omega_nat) (by omega_nat) (by omega_nat), w 2 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 2 4 (by omega_nat) (by omega_nat) (by omega_nat), w 2 3 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 3 6 (by omega_nat) (by omega_nat) (by omega_nat), w 3 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 3 4 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 4 6 (by omega_nat) (by omega_nat) (by omega_nat), w 4 5 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 5 6 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `x23` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h23 : s.gpr .x23 = scr) (hW : H.W ≤ 1024) {s₀ : State}
    (hs : VG.Proof.Pbkdf2.Md.AArch64.Calls.SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Calls.savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Pbkdf2.Md.AArch64.Calls.savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 7, InRegions (t.rd ++ t.wr) (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (VG.Proof.Pbkdf2.Md.AArch64.Calls.slot_in H hsc hL hW hi)
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr .x23 = scr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x23 + BitVec.ofNat 64 o = VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr i := fun h o i ho => by rw [h, ho]
  simp only [Stream.restore, Stream.saved, List.map_cons, List.map_nil]
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea h23 0 (by omega_nat))
    (io rfl rfl 0 (by omega_nat)) fun s₁ u₁ => ?_
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat)
    (ea (by rw [u₁.other _ (by decide), h23]) 1 (by omega_nat)) (io u₁.rd u₁.wr 1 (by omega_nat)) fun s₂ u₂ => ?_
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat)
    (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h23]) 2 (by omega_nat))
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega_nat)) fun s₃ u₃ => ?_
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat)
    (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]) 3 (by omega_nat))
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega_nat)) fun s₄ u₄ => ?_
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have x₄ : s₄.gpr .x23 = scr := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea x₄ 4 (by omega_nat))
    (io r₄ w₄ 4 (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat)
    (ea (by rw [u₅.other _ (by decide), x₄]) 5 (by omega_nat)) (io (u₅.rd.trans r₄) (u₅.wr.trans w₄) 5 (by omega_nat))
    fun s₆ u₆ => ?_
  refine wp_ldr (a := VG.Proof.Pbkdf2.Md.AArch64.Calls.slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat)
    (ea (by rw [u₆.other _ (by decide), u₅.other _ (by decide), x₄]) 6 (by omega_nat))
    (io (u₆.rd.trans (u₅.rd.trans r₄)) (u₆.wr.trans (u₅.wr.trans w₄)) 6 (by omega_nat)) fun s₇ u₇ => ?_
  refine WP.block_nil ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, r₄], by rw [u₇.wr, u₆.wr, u₅.wr, w₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, fun r hr => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.x19]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.x20]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.x22]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x24]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x30]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x23]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2,
      u₁.other r h1]


end VG.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# States and two runs

A streaming state's representation moves with its bytes (`repr_keep`); the
callee-saved registers `x25`–`x28` are never written (`untouched`); and HMAC's
functions are constant time in two runs that agree on their public arguments
(`PubEq`), which are in the argument registers `args`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)

variable {H : Stream} (hH : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK H)

theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

/-- The callee-saved registers we never write. -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28]

/-- The argument registers. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4]

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

end VG.Proof.Pbkdf2.Md.AArch64.Calls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Contract`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the shared contracts

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2ScratchContract` with its facts spelt out, which it implies for
any streaming hash function and scratch space (`generic_implies`). Every
argument is in a register, and the functions `pbkdf2` calls may use the 16
bytes below the stack pointer. Likewise HMAC's `initG` and `finG`
(`Calls.lean`) imply `VG.Spec.Hmac.initScratchContract` and
`VG.Spec.Hmac.finalizeScratchContract` (`initImp`, `finImp`); `initSat` and `finSat`
are states satisfying those contracts' preconditions, from which each hash
function's instance shows them satisfiable.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk initG finG)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space. -/
def pbkG : Contract isa where
  pre s :=
    let pw : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let salt : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let out : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
    let scratch : Region := ⟨s.gpr .x7, W * 8⟩
    16 ≤ s.sp.toNat ∧ s.rd = [pw, salt] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint pw ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint salt ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint out ∧ (VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s).Disjoint scratch ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + W * 8 ≤ 2 ^ 64 ∧
    0 < ((s.gpr .x4).setWidth 32).toNat ∧ (s.gpr .x6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((s.gpr .x4).setWidth 32).toNat (s.gpr .x6).toNat =
      some (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ (s₁.gpr .x4).setWidth 32 = (s₂.gpr .x4).setWidth 32 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- `pbkG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract S W AArch64.abi 16).pre s) :
    (VG.Proof.Pbkdf2.Md.AArch64.pbkG S W).Implies (Spec.Pbkdf2.pbkdf2ScratchContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.AArch64.pbkG, VG.Proof.Pbkdf2.Md.AArch64.Calls.stk, AArch64.abi, AArch64.argRegs] using h

/-! ## HMAC's `init` and `finalize` -/

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x2 => 0x30000 | .x3 => 1 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initScratchContract S W AArch64.abi 16).pre s) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.initG S W).Implies (Spec.Hmac.initScratchContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, VG.Proof.Pbkdf2.Md.AArch64.Calls.initG, VG.Proof.Pbkdf2.Md.AArch64.Calls.stk, AArch64.abi, AArch64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeScratchContract S W AArch64.abi 16).pre s) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.finG S W).Implies (Spec.Hmac.finalizeScratchContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, VG.Proof.Pbkdf2.Md.AArch64.Calls.finG, VG.Proof.Pbkdf2.Md.AArch64.Calls.stk, AArch64.abi, AArch64.argRegs] using h

end VG.Proof.Pbkdf2.Md.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the hash function

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Hash.lean`), `HashOK H` is what the
proofs know of the hash function whose code `H` describes: it is a
Merkle–Damgård hash function `md` (`Md`) whose length field and digest code do
what they should (`Shape`), with a verified compression function (`CompOk`);
its streaming functions are verified against the contracts HMAC's and
PBKDF2's proofs call them with (`stream`, `Calls.lean`); its specification is `md` from the initial
hash value `iv`, with the digest the first `D` bytes of `md`'s; and its sizes
fit.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64 VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (Shape CompOk Sizes)
open VG.Proof.Hmac.Generic.Common (bytesAt_reloc)
open Spec.Hmac (StreamingHash)

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs of `iterate` see it. -/
  md : Md H.P.B H.P.N H.P.L
  shape : Shape md
  /-- The compression function is verified. -/
  comp : CompOk md H.P.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The length field is right for every message shorter than 2⁶⁴ bytes. -/
  lenOk : ∀ n, n < 2 ^ 64 → md.lenOk n
  /-- The streaming functions, verified. -/
  stream : Calls.StreamOK H.stream
  /-- Checked no-clobber facts for the MD wrapper call graph. -/
  initKeepsV : H.initC.allInstrs keepsV = true
  updKeepsV : H.updC.allInstrs keepsV = true
  finKeepsV : H.finC.allInstrs keepsV = true
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m ↔ md.Repr iv mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  /-- The sizes. -/
  sizes : Sizes H.P H.D H.W
  L : 0 < H.P.L ∧ H.P.L ≤ 16
  W : H.W ≤ 256

namespace HashOK

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.AArch64.HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.P.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.P.N + H.P.B := hH.stream.hS
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.P.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B_pos : 0 < H.P.B := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem N_le : H.P.N ≤ 64 := hH.sizes.dims.N.2

/-- What the proof of `iterate` (`Proof/Pbkdf2/AArch64/Iterate.lean`) needs
of the hash function. -/
theorem iterOk : Pbkdf2.AArch64.HashOk H.P H.D H.W hH.SH hH.md hH.iv where
  sizes := hH.sizes
  shape := hH.shape
  reloc := hH.reloc
  lenOk := hH.lenOk _ (by have := hH.B_le; have := hH.sizes.DN; have := hH.N_le; omega)
  link := ⟨hH.hB, hH.hS, hH.hD, fun m p x h => (hH.repr m p x).1 h, hH.hash, hH.sizes.DN,
    by have := hH.sizes.pad; have := hH.sizes.NL; omega⟩

include hH in
/-- The pieces of HMAC's `finalize` after the inner digest write no SIMD
register. -/
theorem finMid_keepsV : H.finMid.all keepsV = true := by
  have hp := Pbkdf2.AArch64.padLen_keepsV (D := H.D) hH.shape
  simp only [Hash.finMid, List.all_append, hp, Bool.and_true]
  simp [Hash.copy32, Impl.Pbkdf2.AArch64.cp32, Impl.MdStream.AArch64.mov, keepsV, vdstOf]

include hH in
theorem cmp_keepsV : (instrs (Impl.MdStream.AArch64.compressAt H.compN H.compC)).all keepsV = true := by
  have hc := hH.comp.keepsV
  rw [Code.allInstrs_eq] at hc
  simp only [Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, instrs, List.all_append, hc,
    Bool.and_true]
  rfl

include hH in
theorem finOut_keepsV : H.finOut.all keepsV = true := by
  have ho := hH.shape.outKeepsV
  by_cases hDN : H.D < H.P.N <;>
  simp only [Hash.finOut, hDN, ↓reduceIte, List.all_append, List.all_cons, ho, Bool.and_true, Bool.true_and] <;>
  simp [Hash.copy32, Impl.Pbkdf2.AArch64.cp32, Impl.Pbkdf2.Md.AArch64.Stream.restore,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.MdStream.AArch64.mov, keepsV, vdstOf]

include hH in
/-- HMAC's `init` writes no SIMD register but in the functions it calls,
which write none either. -/
theorem hmacInit_keepsV : H.hmacInit.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hc := hH.comp.keepsV
  have h1 : H.ipadFill.all keepsV = true := by
    rw [List.all_eq_true]; intro i hi
    simp only [Hash.ipadFill, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | ⟨k, -, rfl⟩) | rfl <;> rfl
  have h2 : H.opadFill.all keepsV = true := by
    rw [List.all_eq_true]; intro i hi
    simp only [Hash.opadFill, Hash.opadW, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | ⟨k, -, rfl | rfl | rfl⟩) | rfl <;> rfl
  rw [Code.allInstrs_eq] at hi hc ⊢
  simp only [Hash.hmacInit, Hash.initKeys, Hash.keyLoop, Impl.Pbkdf2.Md.AArch64.Stream.callInit,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, Hash.stream, instrs,
    List.all_append, hi, hc, h1, h2, Bool.and_true, Bool.true_and]
  simp [Hash.initPrologue, Hash.initOuter, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.save,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.Pbkdf2.Md.AArch64.Stream.restore, Impl.MdStream.AArch64.mov,
    keepsV, vdstOf]

include hH in
/-- HMAC's `finalize` writes no SIMD register but in the functions it calls,
which write none either. -/
theorem hmacFin_keepsV : H.hmacFin.allInstrs keepsV = true := by
  have hf := hH.finKeepsV
  rw [Code.allInstrs_eq] at hf ⊢
  simp only [Hash.hmacFin, Impl.Pbkdf2.Md.AArch64.Stream.callFin, instrs, List.all_append,
    hH.finMid_keepsV, hH.cmp_keepsV, hH.finOut_keepsV, Bool.and_true]
  simp [Hash.stream, hf, Impl.Pbkdf2.Md.AArch64.Stream.finPrologue, Impl.Pbkdf2.Md.AArch64.Stream.save,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.MdStream.AArch64.mov, Impl.MdStream.AArch64.mov, keepsV,
    vdstOf]

include hH in
/-- The MD PBKDF2 wrapper uses only scalar instructions around its certified callees. -/
theorem pbkdf2_keepsV : H.pbkdf2.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hu := hH.updKeepsV
  have hf := hH.finKeepsV
  have ht : H.iterate.allInstrs keepsV = true :=
    Pbkdf2.AArch64.iterate_keepsV hH.shape hH.comp.keepsV
  have hinit : H.hmacInit.allInstrs keepsV = true := hH.hmacInit_keepsV
  have hfin : H.hmacFin.allInstrs keepsV = true := hH.hmacFin_keepsV
  have hk : H.key.allInstrs keepsV = true := by
    simp [Hash.key, Hash.keyShr, Hash.keySub, Hash.short, Hash.hashKey, Hash.hkInit,
      Hash.hkUpd, Hash.hkFin, Hash.hkKey, Impl.MdStream.AArch64.mov,
      Code.allInstrs, keepsV, vdstOf, hi, hu, hf]
  have hs : H.setup.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hinit hu ⊢
    simp [Hash.setup, Hash.initArgs, Hash.saltArgs, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hinit, hu]
  have hb : H.block.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hu hfin ht ⊢
    simp [Hash.block, Hash.intArgs, Hash.finArgs, Hash.iterArgs, Hash.outLen,
      Hash.outLoop, Hash.advance, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hu, hfin, ht]
  simp [Hash.pbkdf2, Hash.entry, Hash.entryPre, Hash.entryPost, Hash.loopRegs,
    Hash.exit, Impl.Pbkdf2.Md.AArch64.Stream.save, Impl.Pbkdf2.Md.AArch64.Stream.saved,
    Impl.Pbkdf2.Md.AArch64.Stream.restore, Impl.MdStream.AArch64.mov,
    Code.allInstrs, keepsV, vdstOf, hk, hs, hb]

end HashOK

end VG.Proof.Pbkdf2.Md.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCommon`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s parts

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/PbkCommon.lean`): the precondition of
`pbkdf2` (`Pre`), the parts of its `scratch`, and what every piece of it keeps
(`KR`): our caller's registers (those we save in `scratch`, and `x25`–`x28`,
which nothing we run writes), `out`, `c - 1` and `out_len` in `scratch`, and
that everything written is in `out`, `scratch` or the 16 bytes below the stack
pointer.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (Sizes)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk SavedRegs SavedRegs.frame saveR)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .x0
abbrev pwl : Nat := (s₀.gpr .x1).toNat
abbrev salt : Addr := s₀.gpr .x2
abbrev sl : Nat := (s₀.gpr .x3).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .x4).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .x5
abbrev ol : Nat := (s₀.gpr .x6).toNat
abbrev scr : Addr := s₀.gpr .x7
abbrev pwR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl s₀⟩
abbrev saltR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl s₀⟩
abbrev outR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol s₀⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, (H.W + H.S) * 8⟩
abbrev stkR : Region := VG.Proof.Pbkdf2.Md.AArch64.Calls.stk s₀
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ o, n⟩
/-- Our caller's registers, `out`, `c - 1` and `out_len`. -/
abbrev hdrR : Region := VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ H.sv 80
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀]
  pw_o : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀)
  pw_s : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀)
  sa_o : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀)
  sa_s : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀)
  o_s : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀)
  stk_pw : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwR s₀)
  stk_sa : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.saltR s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀)
  pwnw : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw s₀).toNat + VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl s₀ ≤ 2 ^ 64
  sanw : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt s₀).toNat + VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl s₀ ≤ 2 ^ 64
  onw : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀).toNat + VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol s₀ ≤ 2 ^ 64
  snw : (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < VG.Proof.Pbkdf2.Md.AArch64.Pbk.cc s₀
  olD : VG.Proof.Pbkdf2.Md.AArch64.Pbk.ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : VG.Proof.Pbkdf2.Md.AArch64.HashOK H) {s₀ : State} (h : (VG.Proof.Pbkdf2.Md.AArch64.pbkG hH.SH (H.W + H.S)).pre s₀) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have hD := hH.hD
  simp only [hD] at h17
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : Sizes H.P H.D H.W
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.psizes (hH : VG.Proof.Pbkdf2.Md.AArch64.HashOK H) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H := ⟨hH.sizes, hH.W⟩

theorem PSizes.N (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 0 < H.P.N ∧ H.P.N ≤ 64 := hz.z.dims.N
theorem PSizes.B_le (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B ≤ 128 := by rcases hz.z.B with h | h <;> omega
theorem PSizes.B_ge (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 56 ∧ H.cO = 8 * H.W + 64 ∧ H.olO = 8 * H.W + 72 ∧
    H.st0O = 8 * H.W + 80 ∧ H.st1O = 8 * H.W + 80 + H.S ∧ H.stSO = 8 * H.W + 80 + 2 * H.S ∧
    H.stWO = 8 * H.W + 80 + 3 * H.S ∧ H.uO = 8 * H.W + 80 + 4 * H.S ∧
    H.tO = 8 * H.W + 80 + 4 * H.S + H.D ∧ H.hkO = 8 * H.W + 80 + 4 * H.S + 2 * H.D ∧
    H.intO = 8 * H.W + 80 + 4 * H.S + 2 * H.D + H.P.N ∧ H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end, and below
4096 (every offset is an immediate). -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 ∧ H.intO + 4 ≤ 4096 := by
  have := hz.N; have := hz.z.DN; have := hz.B_le; have := hz.B_ge; have := hz.W; have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.layout (H := H)
  omega

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.N; have := hz.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ o n) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ a m) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ b n) := by
  have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.L_lt hz; exact Offset.disjoint _ h (by omega) (by omega)

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ b n) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lowR (H := H) s₀) := by
  have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.L_lt hz; exact Offset.disjoint_base _ hb (by omega)

theorem low_sub : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.Pbk.lowR (H := H) s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega)

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ o) n := by
  have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.L_lt hz
  exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega)⟩

include hp in
theorem sc_mem : VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

include hp in
theorem out_mem : VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out`, `c - 1` and `out_len` in `scratch`, and everything written is in
`out`, `scratch` or the 16 bytes below the stack pointer. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x23 : s.gpr .x23 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀
  cs : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Calls.untouched, s.gpr r = s₀.gpr r
  saved : VG.Proof.Pbkdf2.Md.AArch64.Calls.SavedRegs H.hh (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀) s₀ s.mem
  outW : s.mem.readW (VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.outO) 64 = VG.Proof.Pbkdf2.Md.AArch64.Pbk.out s₀
  cW : s.mem.readW (VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.cO) 64 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.Md.AArch64.Pbk.cc s₀ - 1)
  olW : s.mem.readW (VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.olO) 64 = s₀.gpr .x6
  frame : Frame [VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x23, .x25, .x26, .x27, .x28]

theorem kregs_pres : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 80) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ o, 8⟩ (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

theorem save_hdr {s₀ : State} : Region.Sub (VG.Proof.Pbkdf2.Md.AArch64.Calls.saveR H.hh (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀)) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdrR (H := H) s₀) :=
  Offset.sub _ (Nat.le_refl _) (by show 8 * H.W + 56 ≤ 8 * H.W + 80; omega)

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.AArch64.Pbk.Pre (H := H) s₀) (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀], Region.Sub r r') :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (by revert hr; decide +revert)).trans (h.cs r hr),
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left VG.Proof.Pbkdf2.Md.AArch64.Pbk.save_hdr, ?_, ?_, ?_,
    h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)
  · rw [← h.olW]
    exact hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ H.olO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.AArch64.Pbk.hdr_sub (by simp [Hash.olO]) (by simp [Hash.olO])))
      (by decide)

omit hp hz in
theorem KR.same {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (hm ▸ Frame.refl [] s.mem) (fun _ h => by simp at h)
    (fun _ h => by simp at h)

omit hp hz in
theorem KR.upd {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {d : Reg} {v : BitVec 64}
    (u : VG.Proof.MdStream.AArch64.Upd s s' d v) (hd : d ∉ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs, s'.gpr r = s.gpr r) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ o n] s.mem s'.mem) :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.end_le hz).1; simp only [Hash.st0O] at ho; omega) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.AArch64.Pbk.part_sub hon⟩)

omit hz in
theorem stk_sc {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {R : Region} (hR : Region.Sub R (VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀)) :
    (below s.sp 16).Disjoint R := by
  rw [h.sp]; exact hp.stk_s.sub_right hR

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the 16 bytes below the stack pointer. -/
theorem KR.call {s s' : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) {ws : List Region}
    (hf : Frame (ws ++ [below s.sp 16]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s' := by
  have := (VG.Proof.Pbkdf2.Md.AArch64.Pbk.end_le hz).1; have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.layout (H := H)
  have hst : H.sv + 80 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr hsp (fun r hr => hcs r (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_pres r hr).1 (VG.Proof.Pbkdf2.Md.AArch64.Pbk.kregs_pres r hr).2) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.low_disj hz (Nat.le_refl _) (by omega)).sub_right (Region.sub_prefix hk)
      · exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.Pbkdf2.Md.AArch64.Pbk.stk_sc hp h (VG.Proof.Pbkdf2.Md.AArch64.Pbk.part_sub (by rw [hst]; omega))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.AArch64.Pbk.part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.sp]
      exact ⟨_, by simp, fun _ h => h⟩

omit hp hz in
/-- The regions only read are the same as on entry. -/
theorem KR.bytes {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ [VG.Proof.Pbkdf2.Md.AArch64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.AArch64.Pbk.stkR s₀], Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep h.frame hd hn

omit hz in
theorem KR.pwBytes {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) :
    bytesAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl s₀) = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pw s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.pwl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.stk_pw.symm) (by have := hp.pwnw; omega)

omit hz in
theorem KR.saltBytes {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) :
    bytesAt s.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl s₀) = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.AArch64.Pbk.salt s₀) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.stk_sa.symm) (by have := hp.sanw; omega)

omit hz in
theorem in_wr {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) : VG.Proof.Pbkdf2.Md.AArch64.Pbk.scR (H := H) s₀ ∈ s.wr := by rw [h.wr]; exact VG.Proof.Pbkdf2.Md.AArch64.Pbk.sc_mem hp

omit hz in
/-- The parts of `scratch` the functions we call get, as covered regions. -/
theorem cov_part {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (VG.Proof.Pbkdf2.Md.AArch64.Pbk.sR s₀ o n).len ≤ r'.len :=
  sub_of_off (VG.Proof.Pbkdf2.Md.AArch64.Pbk.in_wr hp h) hon

omit hz in
theorem cov_low {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {n : Nat} (hn : n ≤ (H.W + H.S) * 8) :
    ∃ r' ∈ s.wr, ∃ off, (⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨VG.Proof.Pbkdf2.Md.AArch64.Pbk.scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (VG.Proof.Pbkdf2.Md.AArch64.Pbk.in_wr hp h) hn

/-- A part of `scratch`, readable. -/
theorem in_rw {s : State} (h : VG.Proof.Pbkdf2.Md.AArch64.Pbk.KR (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ (H.W + H.S) * 8) :
    InRegions (s.rd ++ s.wr) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.A s₀ o) n :=
  VG.Proof.Hmac.Generic.Common.InRegions.right' ⟨_, VG.Proof.Pbkdf2.Md.AArch64.Pbk.in_wr hp h, Offset.contains_base _ hon
    (by have := VG.Proof.Pbkdf2.Md.AArch64.Pbk.L_lt hz; omega)⟩

end

/-! ## Facts about the offsets

Each proved once, by `omega` on `layout`, for the step proofs: an `omega`
over a step's context, which holds many facts about states and sizes, costs
far more. -/

theorem PSizes.B4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> omega
theorem PSizes.o_B_4_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B + 4 < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_B_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_B_lt_p64 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B < 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_D_le_p64 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D ≤ 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D < 4096 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_p16 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D < 2 ^ 16 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_p64 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D < 2 ^ 64 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_W8_56_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W + 56 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_W8_56_le_outO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W + 56 ≤ H.outO := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_W8_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_W8_le_hkO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_intO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_st0O (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_W8_le_st1O (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_stSO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_sv (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.sv := by
  simp only [Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_W8_le_tO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_W8_le_uO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 8 * H.W ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_cO_64d8_le_outO_24 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.cO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_cO_8_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.cO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.cO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_cO_8_le_olO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.cO + 8 ≤ H.olO := by
  simp only [Hash.cO, Hash.olO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_hkO_D_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.hkO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_hkO_hsF_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.hkO + H.stream.F ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.F = H.P.N := rfl; omega
theorem PSizes.o_hkO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.hkO < 4096 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_intO_4_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_intO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.intO < 4096 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_olO_64d8_le_outO_24 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.olO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_olO_8_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.olO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.olO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_outO_24_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 24 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_outO_24_lt_p64 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 24 < 2 ^ 64 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_outO_64d8_le_outO_24 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 64 / 8 ≤ H.outO + 24 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_outO_8_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_outO_8_le_cO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 8 ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_outO_8_le_olO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO + 8 ≤ H.olO := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_outO_le_cO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_outO_le_olO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO ≤ H.olO := by
  simp only [Hash.outO, Hash.olO, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_st0O_2mS_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + 2 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_st0O_2mS_le_tO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + 2 * H.S ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_3mS_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + 3 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_st0O_S_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_st0O_S_le_hkO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_S_le_st1O (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_S_le_stSO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_le_st0O (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; omega
theorem PSizes.o_st0O_le_st1O (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_le_stSO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O < 4096 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_st0O_lt_p64 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O < 2 ^ 64 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_st1O_S_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_st1O_S_le_hkO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st1O_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st1O_S_le_stSO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st1O_S_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st1O_S_le_uO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st1O_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st1O < 4096 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_stSO_S_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_stSO_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stSO_S_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stSO_hsS_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stSO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO < 4096 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_stWO_S_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_stWO_S_le_intO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stWO_S_le_uO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stWO_hsS_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_hsS_le_hkO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_hsS_le_intO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_le_intO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stWO_le_tO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_stWO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO < 4096 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_sv_80_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.sv + 80 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_tO_D_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.tO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_tO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.tO < 4096 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_uO_D_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.uO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_uO_D_le_tO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.uO + H.D ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_uO_lt_4096 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.uO < 4096 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_outO_mod_8_eq_0 (_hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO % 8 = 0 := by
  simp only [Hash.outO, Hash.sv]; omega
theorem PSizes.o_outO_lt_4096m8 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.outO < 4096 * 8 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_olO_mod_8_eq_0 (_hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.olO % 8 = 0 := by
  simp only [Hash.olO, Hash.sv]; omega
theorem PSizes.o_olO_lt_4096m8 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.olO < 4096 * 8 := by
  simp only [Hash.olO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_B_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B % 4 = 0 := by
  have := hz.B4; omega
theorem PSizes.o_4mSd4_eq_S (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 4 * (H.S / 4) = H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_stSO_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO % 4 = 0 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_stSO_4mSd4_le_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stSO + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_stWO_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO % 4 = 0 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_stWO_4mSd4_le_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_intO_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.intO % 4 = 0 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega
theorem PSizes.o_intO_lt_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.intO < 4096 * 4 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_stWO_le_uO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.stWO ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_4mDd4_eq_D (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 4 * (H.D / 4) = H.D := by
  have := hz.z.D4; omega
theorem PSizes.o_uO_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.uO % 4 = 0 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_uO_4mDd4_le_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.uO + 4 * (H.D / 4) ≤ 4096 * 4 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega
theorem PSizes.o_tO_mod_4_eq_0 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.tO % 4 = 0 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega
theorem PSizes.o_tO_4mDd4_le_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.tO + 4 * (H.D / 4) ≤ 4096 * 4 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.D4; have := hz.z.N4; omega
theorem PSizes.o_cO_mod_8_eq_0 (_hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.cO % 8 = 0 := by
  simp only [Hash.cO, Hash.sv]; omega
theorem PSizes.o_cO_lt_4096m8 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.cO < 4096 * 8 := by
  simp only [Hash.cO, Hash.sv]; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_st0O_S_eq_st1O (_hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + H.S = H.st1O := rfl
theorem PSizes.o_W_le_1024 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.W ≤ 1024 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_st0O_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_le_hkO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_D_le_hsF (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D ≤ H.stream.F := by
  have := hz.z.DN; have : H.stream.F = H.P.N := rfl; omega
theorem PSizes.o_D_le_B (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.D ≤ H.P.B := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_st0O_mod_4_eq_0 (_hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O % 4 = 0 := by
  simp only [Hash.st0O, Hash.sv]; omega
theorem PSizes.o_st0O_4mSd4_le_4096m4 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + 4 * (H.S / 4) ≤ 4096 * 4 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; have := hz.B4; have := hz.z.N4; omega
theorem PSizes.o_B_lt_p16 (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B < 2 ^ 16 := by
  have := hz.z.DN; have := hz.N.2; have := hz.B_le; have := hz.W; omega
theorem PSizes.o_sv_80_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.sv + 80 ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_st0O_3mS_le_stWO (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.st0O + 3 * H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; omega
theorem PSizes.o_B_5_le_L (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : H.P.B + 5 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega
theorem PSizes.o_0_lt_S (hz : VG.Proof.Pbkdf2.Md.AArch64.Pbk.PSizes H) : 0 < H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.DN; have := hz.N.1; have := hz.B_ge; have := hz.z.D0; omega

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s calls

The calls of HMAC's `init` and `finalize` and of `iterate`, whose contracts
(`initG`, `finG`, `iterK`) their proofs are given as hypotheses: each is run
with `WP.callFV` (the callee may use the 16 bytes below the stack pointer, a
frame deep), and shown constant time in two runs with `RelCT.call`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG After frame_depth fdepth_lt ce0 ce1 ce2 ce3 ce4)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.AArch64.HashOK H)

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = out
  x2 : s.gpr .x2 = k
  x3 : (s.gpr .x3).toNat = kl
  x4 : s.gpr .x4 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨out, H.S⟩
  stk_k : (below s.sp 16).Disjoint ⟨k, kl⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := H) s inn out k sc kl) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hB := hH.hB
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4, a.x0, a.x1, a.x2, a.x3, a.x4, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s, a.sp16, a.stk_i, a.stk_o, a.stk_k,
    a.stk_s, a.scnw⟩

theorem hinit_call (hv : Verified AArch64.target H.hmacInit (VG.Proof.Pbkdf2.Md.AArch64.Calls.initG hH.SH H.W)) (hd : H.hmacInit.aarch64Depth ≤ 1)
    {s : State} {inn out k sc : Addr} {kl : Nat} (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s' →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw) a.cw ?_ (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3,
    a.x0, a.x1, a.x2, a.x3] at hpost
  exact hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hd h₄, hvec, hsy⟩ hpost.1 hpost.2

theorem hinit_rel (hv : Verified AArch64.target H.hmacInit (VG.Proof.Pbkdf2.Md.AArch64.Calls.initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := H) s inn out k sc kl ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.InitArgs (H := H) s' inn out k sc kl ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have x3 : s.gpr .x3 = s'.gpr .x3 := BitVec.eq_of_toNat_eq (by rw [a.x3, a'.x3])
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a'.cr a'.cw, a'.cw⟩
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x4, a'.x4, x3, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = outer
  x2 : s.gpr .x2 = cnt
  x3 : s.gpr .x3 = o
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_u : (below s.sp 16).Disjoint ⟨outer, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨o, H.D⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := H) s inn outer cnt o sc) :
    (VG.Proof.Pbkdf2.Md.AArch64.Calls.finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4, a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s, a.sp16, a.stk_i, a.stk_u, a.stk_o,
    a.stk_s, a.scnw⟩

theorem hfin_call (hv : Verified AArch64.target H.hmacFin (VG.Proof.Pbkdf2.Md.AArch64.Calls.finG hH.SH H.W)) (hd : H.hmacFin.aarch64Depth ≤ 1)
    {s : State} {inn outer cnt o sc : Addr}
    (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw) a.cw ?_ (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hd h₄, hvec, hsy⟩ fun k0 text hk hl hi hc ho => ?_
  have hD := hH.hD; have hB := hH.hB
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB] at hpost
  exact hpost k0 text hk hl hi hc ho

theorem hfin_rel (hv : Verified AArch64.target H.hmacFin (VG.Proof.Pbkdf2.Md.AArch64.Calls.finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := H) s inn outer cnt o sc ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.FinArgs (H := H) s' inn outer cnt o sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a'.cr a'.cw, a'.cw⟩
  simp only [VG.Proof.Pbkdf2.Md.AArch64.Calls.finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  x0 : s.gpr .x0 = key
  x1 : s.gpr .x1 = u
  x2 : s.gpr .x2 = n
  x3 : s.gpr .x3 = t
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.IterArgs (H := H) s key u n t sc) :
    (iterK hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4,
    a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s, a.knw, a.scnw⟩

theorem iter_call (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hd : H.iterate.aarch64Depth ≤ 1)
    {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : VG.Proof.Pbkdf2.Md.AArch64.Pbk.IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.AArch64.Calls.After s [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.of_syms (WP.callFV hv.1 (a.pre hH) (VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw) a.cw ?_ (VG.Proof.Pbkdf2.Md.AArch64.Calls.fdepth_lt hd))
  intro s' h₁ h₂ h₃ h₄ h₅ hvec hpost hsy
  refine hQ s' ⟨h₁, h₂, h₃, h₅, VG.Proof.Pbkdf2.Md.AArch64.Calls.frame_depth hd h₄, hvec, hsy⟩ fun k0 hk hi ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB, hS] at hpost
  exact hpost k0 hk hi ho

theorem iter_rel (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.AArch64.Pbk.IterArgs (H := H) s key u n t sc ∧ VG.Proof.Pbkdf2.Md.AArch64.Pbk.IterArgs (H := H) s' key u n t sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.AArch64.Pbk.covers_app a'.cr a'.cw, a'.cw⟩
  simp only [iterK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce0, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce1, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce2, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce3, VG.Proof.Pbkdf2.Md.AArch64.Calls.ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.AArch64.Pbk

end
