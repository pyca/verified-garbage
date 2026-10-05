import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the calls

The contracts the proofs are written against.

* `initK`, `updK` and `finK` are the x86-64 contracts of a hash function's
  streaming `init`, `update` and `finalize`, with the sizes and the
  representation of the streaming state as parameters. At SHA-1 and MD5
  they are the contracts those functions are proved against
  (`Proof/<Alg>/X86_64/Contract.lean`); the SHA-512 family's imply them.
* `initG` and `finG` are those of HMAC's `init` and `finalize`; the
  artifacts are emitted with the shared contracts of `Spec/Hmac/Generic.lean`,
  which imply them (`initImp`, `finImp`, `Contract.lean`). (PBKDF2's
  iteration calls the compression functions directly:
  `Proof/Pbkdf2/X86_64/`.)
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-! ## The functions we call -/

/-- `init(state)`: makes the `S`-byte streaming state at `state` represent the
empty message. -/
def initK (S : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := R s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

/-- `update(state, count, data, len, scratch)`, with `Wb` bytes of scratch
space and one call below it. -/
def updK (S Wb : Nat) (R : Mem → Addr → List Byte → Prop) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    R s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(state, count, out, scratch)`, writing `F` bytes whose first
`D` are the digest `hash m`, for a message of fewer than 2⁶⁴ bytes. -/
def finK (S Wb F D : Nat) (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) :
    Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, S⟩
    let out : Region := ⟨s.gpr .rdx, F⟩
    let scratch : Region := ⟨s.gpr .rcx, Wb⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, R s.mem (s.gpr .rdi) m → m.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 m.length → (bytesAt s'.mem (s.gpr .rdx) F).take D = hash m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## HMAC's functions

`S` is a streaming hash function and `W` the number of 64-bit words of
scratch space. The contracts let each function use the 16 bytes of stack
below its return address for its calls. -/

variable (S : StreamingHash) (W : Nat)

/-- `init(inner, outer, key, key_len, scratch)`: `VG.Spec.Hmac.initScratchContract`. -/
def initG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    (s.gpr .rcx).toNat ≤ S.H.blockSize ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `finalize(inner, outer, count, out, scratch)`: `VG.Spec.Hmac.finalizeScratchContract`. -/
def finG : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let out : Region := ⟨s.gpr .rcx, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
    outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' := ∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
    S.Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (S.H.blockSize + text.length) →
    S.Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) S.digestBytes = hmacBlockKey S.H k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# The streaming functions, called

`StreamOK H` is what the proofs know of the streaming functions `H` of a
hash function: they are verified against `initK`, `updK` and `finK`, the
representation of the streaming state is determined by the state's bytes,
and the sizes are small. From it, each call is run with `WP.call`, and shown
constant time in two runs with `RelCT.call`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- A streaming hash function's x86-64 functions, verified. `Wb` is the
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
  hW : H.W ≤ 256
  /-- The representation depends only on the state's bytes. -/
  repr : ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < H.S, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    SH.Repr m p msg → SH.Repr m' q msg
  init : Verified X86_64.target H.initC (VG.Proof.Pbkdf2.Md.X86_64.Calls.initK H.S SH.Repr)
  upd : Verified X86_64.target H.updC (VG.Proof.Pbkdf2.Md.X86_64.Calls.updK H.S Wb SH.Repr)
  fin : Verified X86_64.target H.finC (VG.Proof.Pbkdf2.Md.X86_64.Calls.finK H.S Wb H.F H.D SH.Repr SH.H.hash)
  initDepth : H.initC.depth ≤ 1
  updDepth : H.updC.depth ≤ 1
  finDepth : H.finC.depth ≤ 1
  initSp : NoSp H.initC
  updSp : NoSp H.updC
  finSp : NoSp H.finC

variable {H : Stream} (hH : VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK H)

/-- What a call leaves: the regions, the callee-saved registers, and memory
outside what it may write. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below (s.gpr .rsp) 16]) s.mem s'.mem

/-- The stack of a call nested at most one deep. -/
theorem frame_depth {c : Prog isa} (hd : c.depth ≤ 1) {s : State} {ws : List Region} {m' : Mem}
    (h : Frame (ws ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem m') :
    Frame (ws ++ [below (s.gpr .rsp) 16]) s.mem m' :=
  h.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega_nat) (by omega_nat)⟩

/-- A region disjoint from the 16 bytes below `rsp` reads the same on entry
to a callee. -/
theorem callEntry_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    s.callEntry.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
  Proof.Sha256.X86_64.Stream.callEntry_byte s (R := ⟨p, n⟩)
    (hd.sub_left (below_sub (by omega_nat) (by omega_nat))) hn hi

theorem ret_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 16) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega_nat) (by omega_nat)

theorem stk_sub (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 16) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 8 = s.gpr .rsp - BitVec.ofNat 64 16 from Offset.sub_sub_ofNat _ 8 8]
  exact Offset.sub_below _ (a := 16) (by omega_nat) (by omega_nat)

theorem covers_wr {ws : List Region} {s : State} (h : Covers ws s.wr) : Covers ([] ++ ws) (s.rd ++ s.wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n (by simpa using hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ne_rsp {r : Reg} (h : r ≠ .rsp) (s : State) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-! ## `init` -/

theorem init_call {s : State} {st : Addr} (hdi : s.gpr .rdi = st) (hc : Covers [⟨st, H.S⟩] s.wr)
    (hstk : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.Calls.After s [⟨st, H.S⟩] s' → hH.SH.Repr s'.mem st [] → Q s') :
    WP isa (.call H.initN H.initC) s Q := by
  refine WP.call (k := VG.Proof.Pbkdf2.Md.X86_64.Calls.initK H.S hH.SH.Repr) hH.init.1 hH.initSp (by have := hH.initDepth; omega_nat)
    (rd := []) (wr := [⟨st, H.S⟩]) ?_ (VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr hc) hc ?_
  · refine ⟨rfl, by simp [VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi], ?_⟩
    simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi]
    exact hstk.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s)
  · intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
    refine hQ s' ⟨h₁, h₂, h₃, VG.Proof.Pbkdf2.Md.X86_64.Calls.frame_depth hH.initDepth h₄⟩ ?_
    simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.initK, State.withRegions_gpr, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), hdi, hm] at hpost
    exact hpost

/-! ## `update` -/

/-- The regions of a call of `update`. -/
structure UpdArgs (s : State) (st d sc : Addr) (len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = d
  rcx : (s.gpr .rcx).toNat = len
  r8 : s.gpr .r8 = sc
  cd : Covers [⟨d, len⟩] (s.rd ++ s.wr)
  cw : Covers [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s.wr
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  d_st : Region.Disjoint ⟨d, len⟩ ⟨st, H.S⟩
  d_sc : Region.Disjoint ⟨d, len⟩ ⟨sc, hH.Wb⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩
  stk_d : (below (s.gpr .rsp) 16).Disjoint ⟨d, len⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, hH.Wb⟩

theorem UpdArgs.covers {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH s st d sc len) :
    Covers ([⟨d, len⟩] ++ [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) (s.rd ++ s.wr) :=
  fun a n hi => by
    rcases List.mem_append.mp (show _ ∈ _ from hi.choose_spec.1) with hr | hr
    · exact h.cd a n ⟨_, hr, hi.choose_spec.2⟩
    · obtain ⟨r, hr', hc⟩ := h.cw a n ⟨_, hr, hi.choose_spec.2⟩
      exact ⟨r, List.mem_append_right _ hr', hc⟩

theorem UpdArgs.pre {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH s st d sc len) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.updK H.S hH.Wb hH.SH.Repr).pre (s.callEntry.withRegions [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rdx, h.rcx, h.r8]
  exact ⟨by trivial, by trivial, h.st_sc, h.d_st, h.d_sc, h.stk_st.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s), h.stk_sc.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s),
    h.stk_st.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s), h.stk_d.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s), h.stk_sc.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s)⟩

theorem upd_call {s : State} {st d sc : Addr} {len : Nat} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH s st d sc len)
    (hlen : len ≤ 2 ^ 64) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.Calls.After s [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .rsi = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem d len)) → Q s') :
    WP isa (.call H.updN H.updC) s Q := by
  refine WP.call (k := VG.Proof.Pbkdf2.Md.X86_64.Calls.updK H.S hH.Wb hH.SH.Repr) hH.upd.1 hH.updSp (by have := hH.updDepth; omega_nat)
    (h.pre hH) (h.covers hH) h.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' ⟨h₁, h₂, h₃, VG.Proof.Pbkdf2.Md.X86_64.Calls.frame_depth hH.updDepth h₄⟩ fun m hr hc => ?_
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.updK, State.withRegions_gpr, State.withRegions_mem, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rdx, h.rcx, hm] at hpost
  have hS := hH.hSB
  have e : bytesAt s.callEntry.mem d len = bytesAt s.mem d len := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => VG.Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_d hlen (List.mem_range.mp hi)
  rw [← e]
  exact hpost m (hH.repr _ _ _ _ _ (fun i hi => VG.Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_st (by omega_nat) hi) hr) hc

/-! ## `finalize` -/

/-- The regions of a call of `finalize`. -/
structure FinArgs (s : State) (st o sc : Addr) : Prop where
  rdi : s.gpr .rdi = st
  rdx : s.gpr .rdx = o
  rcx : s.gpr .rcx = sc
  cw : Covers [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s.wr
  st_o : Region.Disjoint ⟨st, H.S⟩ ⟨o, H.F⟩
  st_sc : Region.Disjoint ⟨st, H.S⟩ ⟨sc, hH.Wb⟩
  o_sc : Region.Disjoint ⟨o, H.F⟩ ⟨sc, hH.Wb⟩
  stk_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩
  stk_o : (below (s.gpr .rsp) 16).Disjoint ⟨o, H.F⟩
  stk_sc : (below (s.gpr .rsp) 16).Disjoint ⟨sc, hH.Wb⟩

theorem FinArgs.pre {s : State} {st o sc : Addr} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH s st o sc) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash).pre
      (s.callEntry.withRegions [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩]) := by
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rdx, h.rcx]
  exact ⟨by trivial, by trivial, h.st_o, h.st_sc, h.o_sc, h.stk_st.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s),
    h.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s), h.stk_sc.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub s), h.stk_st.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s),
    h.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s), h.stk_sc.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.stk_sub s)⟩

theorem fin_call {s : State} {st o sc : Addr} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH s st o sc) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.Calls.After s [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] s' →
      (∀ m, hH.SH.Repr s.mem st m → m.length < 2 ^ 64 → s.gpr .rsi = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem o H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) s Q := by
  refine WP.call (k := VG.Proof.Pbkdf2.Md.X86_64.Calls.finK H.S hH.Wb H.F H.D hH.SH.Repr hH.SH.H.hash) hH.fin.1 hH.finSp
    (by have := hH.finDepth; omega_nat) (h.pre hH) (VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr h.cw) h.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' ⟨h₁, h₂, h₃, VG.Proof.Pbkdf2.Md.X86_64.Calls.frame_depth hH.finDepth h₄⟩ fun m hr hl hc => ?_
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finK, State.withRegions_gpr, State.withRegions_mem, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rdx, hm] at hpost
  have hS := hH.hSB
  exact hpost m (hH.repr _ _ _ _ _ (fun i hi => VG.Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s h.stk_st (by omega_nat) hi) hr) hl hc

/-! ## The calls in two runs

A call is constant time when the callee's precondition holds in both runs
and its public arguments agree (`RelCT.call`). -/

include hH in
theorem init_rel {P : State → State → Prop} {st : Addr}
    (h : ∀ s s', P s s' → s.gpr .rdi = st ∧ s'.gpr .rdi = st ∧ Covers [⟨st, H.S⟩] s.wr ∧
      Covers [⟨st, H.S⟩] s'.wr ∧ (below (s.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ ∧
      (below (s'.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  refine RelCT.call hH.init.1 hH.init.2.1 [] [⟨st, H.S⟩] fun s s' hp => ?_
  obtain ⟨d, d', c, c', k, k', sp⟩ := h s s' hp
  have pre : ∀ t : State, t.gpr .rdi = st → (below (t.gpr .rsp) 16).Disjoint ⟨st, H.S⟩ →
      (VG.Proof.Pbkdf2.Md.X86_64.Calls.initK H.S hH.SH.Repr).pre (t.callEntry.withRegions [] [⟨st, H.S⟩]) := fun t hd hk => by
    refine ⟨rfl, by simp [VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), hd], ?_⟩
    simp only [State.withRegions_gpr, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), hd]
    exact hk.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.ret_sub t)
  exact ⟨pre s d k, pre s' d' k', by
    simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.initK, State.withRegions_gpr, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), d, d'],
    VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr c, c, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr c', c', sp⟩

theorem upd_rel {P : State → State → Prop} {st d sc : Addr} {len : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH s st d sc len ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.UpdArgs hH s' st d sc len ∧
      s.gpr .rsi = s'.gpr .rsi ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.updN H.updC) fun _ _ => True := by
  refine RelCT.call hH.upd.1 hH.upd.2.1 [⟨d, len⟩] [⟨st, H.S⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', si, sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  refine ⟨a.pre hH, a'.pre hH, ?_, a.covers hH, a.cw, a'.covers hH, a'.cw, sp⟩
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.updK, State.withRegions_gpr, State.callEntry_rsp, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rdx, a'.rdx,
    a.r8, a'.r8, si, cx, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem fin_rel {P : State → State → Prop} {st o sc : Addr}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH s st o sc ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH s' st o sc ∧
      s.gpr .rsi = s'.gpr .rsi ∧ s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.finN H.finC) fun _ _ => True := by
  refine RelCT.call hH.fin.1 hH.fin.2.1 [] [⟨st, H.S⟩, ⟨o, H.F⟩, ⟨sc, hH.Wb⟩] fun s s' hp => ?_
  obtain ⟨a, a', si, sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr a.cw, a.cw, VG.Proof.Pbkdf2.Md.X86_64.Calls.covers_wr a'.cw, a'.cw, sp⟩
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finK, State.withRegions_gpr, State.callEntry_rsp, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a'.rdi, a.rdx, a'.rdx, a.rcx, a'.rcx, si, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_taint {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2))
    hc).wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A call, in two runs each described by `WP`. -/
theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun s s' => F s ∧ F' s') c fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' :=
  (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Pbkdf2.Md.X86_64.Calls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: what the proofs share

The byte copy (`copy`), used for states, digests and `U`, a loop that counts
`r14` up from 0 and ends when it reaches its bound; the registers of our
caller, stored in `scratch` after the working space of the functions we call
(`Stream.saved`) and loaded back at the end; and facts about two runs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream byteAt copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeW8_apply)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32i wp_addi wp_cmp wp_cmpi wp_movzx8 wp_store8
  ofNat_succ sub_beq)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open Spec.Sha256 (bytesAt)

/-! ## Arithmetic -/

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_nat)]
  exact VG.Proof.Pbkdf2.Md.X86_64.Calls.zx_ofNat (by omega_nat)

theorem sx_one : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem ea_byteAt (s : State) (b : Reg) (o k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea (byteAt b o) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  simp only [State.ea, byteAt, h14, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-- `r14` counted up to `n`: the flags after `add r14, 1; cmp r14, n`. -/
theorem count_zf {k n : Nat} (hk : k < n) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 - (BitVec.ofNat 32 n).signExtend 64 == 0) =
      decide (k + 1 = n) := by
  rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_ofNat hn, ← ofNat_succ, sub_beq (by omega_nat) (by omega_nat)]

/-! ## `copy` -/

/-- After `k` bytes of `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = VG.WriteBytes.writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ≠ .rax ∧ src ≠ .r14) (hd : dst ≠ .rax ∧ dst ≠ .r14)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 so, n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      VG.Proof.Pbkdf2.Md.X86_64.Calls.Copied s (s.gpr dst + BitVec.ofNat 64 d) (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) n) t := by
  set A := s.gpr src + BitVec.ofNat 64 so
  set B := s.gpr dst + BitVec.ofNat 64 d
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : VG.Proof.Pbkdf2.Md.X86_64.Calls.CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩
  refine WP.mono (VG.Proof.Pbkdf2.Md.X86_64.Calls.count_loop hn (VG.Proof.Pbkdf2.Md.X86_64.Calls.CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k) (by rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.ea_byteAt _ _ _ _ h.r14, h.other _ hs.1 hs.2])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ hd.1,
      h.other _ hd.1 hd.2]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_one, ← ofNat_succ], ?_⟩, by rw [z₄, h14, VG.Proof.Pbkdf2.Md.X86_64.Calls.count_zf hk hn']⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, bytesAt_snoc']
  have e : VG.WriteBytes.writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [VG.WriteBytes.writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have e' := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega_nat)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']


/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ v).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.imm v) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem xor_byte (b : Byte) (v : BitVec 32) :
    ((((b.setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

end VG.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# Our caller's registers

The six callee-saved registers we use are stored in `scratch` after the
working space of the functions we call (`Stream.saved`), and loaded back at
the end.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.MdStream.X86_64 (at_)
open VG.Proof.MdStream.X86_64 (ea_at)
open VG.Proof.Sha256.X86_64 (ofInt_natCast contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_store wp_movm)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Stream)

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 48⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 0) 64 = s₀.gpr .rbx
  rbp : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 1) 64 = s₀.gpr .rbp
  r12 : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 2) 64 = s₀.gpr .r12
  r13 : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 3) 64 = s₀.gpr .r13
  r14 : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 4) 64 = s₀.gpr .r14
  r15 : m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 5) 64 = s₀.gpr .r15

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 6) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i, 8⟩ (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H scr) := by
  rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.slot, ← add_ofNat_add]
  exact Proof.Sha256.X86_64.sub_offset (by omega_nat) (by omega_nat)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (hij : i ≠ j) (hW : H.W ≤ 256) :
    Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i, 8⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, VG.Proof.Pbkdf2.Md.X86_64.Calls.slot] at h₁ h₂
  rw [← BitVec.sub_sub] at h₁ h₂
  generalize a - scr = y at h₁ h₂
  rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega_nat)] at h₁ h₂
  have := y.isLt
  omega_nat

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H scr).Disjoint r) :
    VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H scr s₀ m' := by
  have k : ∀ i < 6, m'.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 64 = m.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega_nat), h.rbx], by rw [k 1 (by omega_nat), h.rbp], by rw [k 2 (by omega_nat), h.r12],
    by rw [k 3 (by omega_nat), h.r13], by rw [k 4 (by omega_nat), h.r14], by rw [k 5 (by omega_nat), h.r15]⟩

theorem ea_slot (s : State) (b : Reg) (scr : Addr) (hb : s.gpr b = scr) (i : Nat) :
    s.ea (at_ b (8 * H.W + 8 * i)) = VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i := by
  rw [ea_at, ofInt_natCast, hb]

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 48 ≤ L)
    (hW : H.W ≤ 256) {i : Nat} (hi : i < 6) : InRegions rs (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega_nat) (by omega_nat)⟩

/-- Saving the registers, with `scratch` in `r8`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h8 : s.gpr .r8 = scr) (hW : H.W ≤ 256)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → Frame [VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H scr] s.mem s'.mem →
      VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 6, InRegions t.wr (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact VG.Proof.Pbkdf2.Md.X86_64.Calls.slot_in H hsc hL hW hi
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ i, t.ea (at_ .r8 (8 * H.W + 8 * i)) = VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i :=
    fun hg i => by rw [ea_at, ofInt_natCast, hg, h8]
  simp only [Stream.save, Stream.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 0) (ea rfl 0) (io rfl 0 (by omega_nat)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 1) (ea g₁ 1) (io wr₁ 1 (by omega_nat)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 2) (ea (g₂.trans g₁) 2) (io (wr₂.trans wr₁) 2 (by omega_nat))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 3) (ea (g₃.trans (g₂.trans g₁)) 3) (io (wr₃.trans (wr₂.trans wr₁)) 3 (by omega_nat))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 4) (ea (g₄.trans (g₃.trans (g₂.trans g₁))) 4)
    (io (wr₄.trans (wr₃.trans (wr₂.trans wr₁))) 4 (by omega_nat)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 5) (ea (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁)))) 5)
    (io (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans wr₁)))) 5 (by omega_nat)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have g : s₆.gpr = s.gpr := g₆.trans (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁))))
  refine k s₆ g (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_ ?_
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    have c : ∀ i < 6, (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H scr).Contains (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) (64 / 8) := fun i hi => by
      rw [VG.Proof.Pbkdf2.Md.X86_64.Calls.slot, ← add_ofNat_add]; exact contains_offset (by omega_nat) (by omega_nat)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 3 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 5 (by omega_nat)))
  · have d : ∀ i j, i < 6 → j < 6 → i ≠ j → Region.Disjoint ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i, 8⟩ ⟨VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr j, 8⟩ :=
      fun i j hi hj hij => VG.Proof.Pbkdf2.Md.X86_64.Calls.slot_disj H scr hi hj hij hW
    rw [m₆, m₅, m₄, m₃, m₂, m₁, g₅, g₄, g₃, g₂, g₁]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readW_writeW_ne _ _ (d 0 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 3 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 2 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 1 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 1 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 3 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 2 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 2 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 2 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 2 3 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 3 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 3 4 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 4 5 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `r15` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h15 : s.gpr .r15 = scr) (hW : H.W ≤ 256) {s₀ : State}
    (hs : VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 6, InRegions (t.rd ++ t.wr) (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot_in H hsc hL hW hi)
  have ea : ∀ {t : State}, t.gpr .r15 = scr → ∀ i, t.ea (at_ .r15 (8 * H.W + 8 * i)) = VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i :=
    fun h i => by rw [ea_at, ofInt_natCast, h]
  simp only [Stream.restore, Stream.saved, List.map_cons, List.map_nil]
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 0) (ea h15 0) (io rfl rfl 0 (by omega_nat)) fun s₁ u₁ => ?_
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 1) (ea (by rw [u₁.other _ (by decide), h15]) 1)
    (io u₁.rd u₁.wr 1 (by omega_nat)) fun s₂ u₂ => ?_
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 2) (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h15]) 2)
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega_nat)) fun s₃ u₃ => ?_
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 3) (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
                                    u₁.other _ (by decide), h15]) 3)
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega_nat)) fun s₄ u₄ => ?_
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 4) (ea (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
                                    u₂.other _ (by decide), u₁.other _ (by decide), h15]) 4)
    (io (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))) (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))) 4
      (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_movm (a := VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr 5) (ea (by rw [u₅.other _ (by decide), u₄.other _ (by decide),
                                    u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]) 5)
    (io (u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))))
      (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))) 5 (by omega_nat)) fun s₆ u₆ => ?_
  refine WP.block_nil ⟨by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun r hr => ?_⟩
  · have hm : ∀ t : State, t.mem = s.mem → ∀ i, t.mem.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 64 = s.mem.readW (VG.Proof.Pbkdf2.Md.X86_64.Calls.slot H scr i) 64 :=
      fun t h i => by rw [h]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, hs.rbx]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, hs.rbp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        hs.r12]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hs.r13]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r14]
    · rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r15]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]


end VG.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# States and two runs

A streaming state's representation moves with its bytes (`repr_keep`); and
HMAC's functions are constant time in two runs that agree on their public
arguments (`PubEq`), which are in the argument registers `args`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

variable {H : Stream} (hH : VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK H)

theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

/-- The argument registers. -/
abbrev args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

end VG.Proof.Pbkdf2.Md.X86_64.Calls

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Contract`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the shared contracts

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2ScratchContract` with its facts spelt out, which it implies for
any streaming hash function and scratch space (`generic_implies`), as HMAC's
`initG` and `finG` (`Calls.lean`) imply `VG.Spec.Hmac.initScratchContract` and
`VG.Spec.Hmac.finalizeScratchContract` (`initImp`, `finImp`). `initSat` and `finSat`
are states satisfying HMAC's shared contracts' preconditions, from which each
hash function's instance shows them satisfiable.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space and three calls below it. -/
def pbkG : Contract isa where
  pre s :=
    let outLen := stackArg s 0
    let sc := stackArg s 1
    let pw : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let salt : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let out : Region := ⟨s.gpr .r9, outLen.toNat⟩
    let scratch : Region := ⟨sc, W * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 24, 24⟩
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧
    s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + outLen.toNat ≤ 2 ^ 64 ∧ sc.toNat + W * 8 ≤ 2 ^ 64 ∧
    0 < ((s.gpr .r8).setWidth 32).toNat ∧ outLen.toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    let outLen := stackArg s 0
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat outLen.toNat =
      some (bytesAt s'.mem (s.gpr .r9) outLen.toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem map_range2 {α : Type} (f : Nat → α) : List.map f (List.range 2) = [f 0, f 1] := rfl

/-- `pbkG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2ScratchContract S W X86_64.abi 24).pre s) :
    (VG.Proof.Pbkdf2.Md.X86_64.pbkG S W).Implies (Spec.Pbkdf2.pbkdf2ScratchContract S W X86_64.abi 24) := by
  exact
    { pre := by
        intro s h
        -- Twice: the stack arguments' list evaluates only on the second pass.
        sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq] at h
        sig_pre [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      post := by
        rintro s s' - h
        sig_post [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq]
        sig_reduce [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, VG.Proof.Pbkdf2.Md.X86_64.pbkG, X86_64.abi, X86_64.argRegs, VG.Proof.Pbkdf2.Md.X86_64.map_range2, List.append_eq] at h
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h
        sig_split h
        rename_i h1 h2 h3 h4 h5 h6 h7 h8
        exact ⟨h2, h3, h4, h5, h6, h7, h8, h, h1⟩
      sat := h }

/-! ## HMAC's `init` and `finalize` -/

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 1 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initScratchContract S W X86_64.abi 16).pre s) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.initG S W).Implies (Spec.Hmac.initScratchContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost, VG.Proof.Pbkdf2.Md.X86_64.Calls.initG, X86_64.abi, X86_64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeScratchContract S W X86_64.abi 16).pre s) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.finG S W).Implies (Spec.Hmac.finalizeScratchContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, VG.Proof.Pbkdf2.Md.X86_64.Calls.finG, X86_64.abi, X86_64.argRegs] using h

end VG.Proof.Pbkdf2.Md.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash`. -/
section

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the hash function

`HashOK H` is what the proofs know of the hash function whose code `H`
describes: its streaming code is the generic Merkle–Damgård code
(`Proof/MdStream/X86_64/`) for a hash function `md` (`Md`) whose pieces do
what they should (`Shape`, `Taints`), calling a verified compression function
(`CalleeOk`); its specification `SH` is `md` from the initial hash value `iv`,
with the digest the first `D` bytes of `md`'s; its streaming `init` is
verified; and its sizes fit.

From it, the streaming functions are verified against the contracts HMAC's
and PBKDF2's proofs call them with (`HashOK.stream`, `Calls.lean`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initK)
open VG.Proof.Hmac.Generic.Common (bytesAt_reloc)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the streaming proofs see it. -/
  md : Md H.P.B H.P.N H.P.L
  dims : Dims H.P
  shape : Shape md
  taints : Taints H.P
  /-- The compression function is verified. -/
  comp : CalleeOk md H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : ∀ (m m' : Mem) (p q : Addr), (∀ i < H.P.N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    md.stateAt m' q = md.stateAt m p
  /-- The length field is right for every message shorter than 2⁶⁴ bytes. -/
  lenOk : ∀ n, n < 2 ^ 64 → md.lenOk n
  /-- The specification: `md` from `iv`, with a `D`-byte digest. -/
  SH : StreamingHash
  iv : md.HV
  repr : ∀ mem p m, SH.Repr mem p m ↔ md.Repr iv mem p m
  hash : ∀ m, SH.H.hash m = (md.hash iv m).take H.D
  hB : SH.H.blockSize = H.P.B
  hS : SH.stateBytes = H.P.N + H.P.B
  hD : SH.digestBytes = H.D
  /-- The sizes: the digest is whole 32-bit words of the hash value, and a
  block holds it with its padding; the saved registers are aligned. -/
  hD0 : 0 < H.D
  hDN : H.D ≤ H.P.N
  hD4 : H.D % 4 = 0
  hN4 : H.P.N % 4 = 0
  hDL : H.D + H.P.L + 4 ≤ H.P.B
  hL4 : H.P.L % 4 = 0
  hNL : H.P.N + H.P.L ≤ H.P.B
  hso : H.P.so % 8 = 0 ∧ H.P.so + 48 ≤ 8 * 256
  /-- The working space our functions get holds `iterate`'s. -/
  fits : H.P.so + 48 + H.P.N + H.P.B ≤ 8 * H.W
  hW : H.W ≤ 256
  /-- The streaming `init`. -/
  init : Verified X86_64.target H.initC (VG.Proof.Pbkdf2.Md.X86_64.Calls.initK (H.P.N + H.P.B) SH.Repr)
  initDepth : H.initC.depth ≤ 1
  initSp : NoSp H.initC
  /-- Facts about the streaming `update` and `finalize` that the kernel
  checks for each hash function: they never load MXCSR (so they keep its
  control bits) or write `rsp`, and make calls one deep. -/
  updMx : H.updC.allInstrs (fun i => !loadsMxcsr i) = true
  finMx : H.finC.allInstrs (fun i => !loadsMxcsr i) = true
  updSp : NoSp H.updC
  finSp : NoSp H.finC
  updDepth : H.updC.depth ≤ 1
  finDepth : H.finC.depth ≤ 1

namespace HashOK

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H)

include hH in
theorem B_le : H.P.B ≤ 128 := by rcases hH.dims.B with h | h <;> omega

include hH in
theorem B_pos : 0 < H.P.B := hH.dims.pos

include hH in
theorem N_le : H.P.N ≤ 64 := hH.dims.N.2

/-- The representation moves with the state's bytes. -/
theorem md_reloc {m m' : Mem} {p q : Addr} {msg : List Byte} {iv : hH.md.HV}
    (h : ∀ i < H.P.N + H.P.B, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : hH.md.Repr iv m p msg) : hH.md.Repr iv m' q msg := by
  have hB := hH.B_pos
  refine ⟨by rw [hH.reloc m m' p q fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  exact bytesAt_reloc h (o := H.P.N) (k := msg.length % H.P.B) (by have := Nat.mod_lt msg.length hB; omega)

theorem sh_reloc (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < H.P.N + H.P.B, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : hH.SH.Repr m p msg) : hH.SH.Repr m' q msg :=
  (hH.repr _ _ _).2 (hH.md_reloc h ((hH.repr _ _ _).1 hr))

/-! ## The streaming functions -/

/-- `update` is verified against the contract HMAC's proofs call it with. -/
theorem upd : Verified X86_64.target H.updC
    (Calls.updK (H.P.N + H.P.B) (H.P.so + 48) hH.SH.Repr) :=
  Verified.of_implies (MdStream.X86_64.Update.verified hH.dims hH.taints hH.comp hH.updMx)
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => (hH.repr _ _ _).2 (h hH.iv m ((hH.repr _ _ _).1 hr) hc)
      pub := fun _ _ _ _ h => h
      sat := (MdStream.X86_64.Update.verified hH.dims hH.taints hH.comp hH.updMx).2.2 }

/-- `finalize` is verified against the contract HMAC's proofs call it with:
its first `D` bytes are the digest. -/
theorem fin : Verified X86_64.target H.finC
    (Calls.finK (H.P.N + H.P.B) (H.P.so + 48) H.P.N H.D hH.SH.Repr hH.SH.H.hash) :=
  Verified.of_implies (MdStream.X86_64.Finalize.verified hH.dims hH.shape hH.taints hH.comp hH.finMx)
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hl hc => by
        rw [hH.hash, h hH.iv m ((hH.repr _ _ _).1 hr) (hH.lenOk _ hl) hc]
      pub := fun _ _ _ _ h => h
      sat := (MdStream.X86_64.Finalize.verified hH.dims hH.shape hH.taints hH.comp hH.finMx).2.2 }

/-- The streaming functions, as HMAC's and PBKDF2's proofs call them. -/
def stream : Calls.StreamOK H.stream where
  SH := hH.SH
  Wb := H.P.so + 48
  hS := hH.hS
  hD := hH.hD
  hB := hH.hB
  hDF := hH.hDN
  hF := hH.N_le
  hD0 := hH.hD0
  hS0 := by show 0 < H.P.N + H.P.B; have := hH.B_pos; omega
  hSB := by show H.P.N + H.P.B ≤ 256; have := hH.B_le; have := hH.N_le; omega
  hB0 := hH.B_pos
  hBB := hH.B_le
  hWb := by show H.P.so + 48 ≤ 8 * ((H.P.so + 48) / 8); have := hH.hso; omega
  hW := by show (H.P.so + 48) / 8 ≤ 256; have := hH.hso; omega
  repr := hH.sh_reloc
  init := hH.init
  upd := hH.upd
  fin := hH.fin
  initDepth := hH.initDepth
  updDepth := hH.updDepth
  finDepth := hH.finDepth
  initSp := hH.initSp
  updSp := hH.updSp
  finSp := hH.finSp

end HashOK

/-! ## The sizes -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (H : Hash) : Prop where
  B : H.P.B = 64 ∨ H.P.B = 128
  N : 0 < H.P.N ∧ H.P.N ≤ 64
  L : 0 < H.P.L ∧ H.P.L ≤ 16
  D : 0 < H.D ∧ H.D ≤ H.P.N ∧ H.D % 4 = 0 ∧ H.D + H.P.L + 4 ≤ H.P.B
  N4 : H.P.N % 4 = 0
  L4 : H.P.L % 4 = 0
  NL : H.P.N + H.P.L ≤ H.P.B
  so : H.P.so % 8 = 0 ∧ H.P.so ≤ 2048
  fits : H.P.so + 48 + H.P.N + H.P.B ≤ 8 * H.W
  W : H.W ≤ 256

theorem Sizes.B_le {H : Hash} (hz : VG.Proof.Pbkdf2.Md.X86_64.Sizes H) : H.P.B ≤ 128 := by rcases hz.B with h | h <;> omega

theorem HashOK.sizes {H : Hash} (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H) : VG.Proof.Pbkdf2.Md.X86_64.Sizes H :=
  ⟨hH.dims.B, hH.dims.N, hH.dims.L, ⟨hH.hD0, hH.hDN, hH.hD4, hH.hDL⟩, hH.hN4, hH.hL4, hH.hNL,
    ⟨hH.hso.1, hH.dims.so⟩, hH.fits, hH.hW⟩

/-- What the proof of PBKDF2's iteration (`Proof/Pbkdf2/X86_64/Iterate.lean`)
needs of the hash function, with `W` words of scratch space. -/
theorem HashOK.iterOk {H : Hash} (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H) :
    Pbkdf2.X86_64.HashOk H.P H.D H.W hH.SH hH.md hH.iv where
  sizes := ⟨hH.dims, hH.hN4, hH.hD4, hH.hL4, hH.hD0, hH.hDN, hH.hNL, by have := hH.hDL; omega, hH.fits,
    by have := hH.hW; omega⟩
  shape := hH.shape
  reloc := hH.reloc
  lenOk := hH.lenOk _ (by have := hH.B_le; have := hH.hDN; have := hH.N_le; omega)
  link := ⟨hH.hB, hH.hS, hH.hD, fun m p x h => (hH.repr m p x).1 h, hH.hash, hH.hDN,
    by have := hH.hDL; omega⟩

end VG.Proof.Pbkdf2.Md.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.HmacFinInner`. -/
section

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize` up to the inner digest

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by saving our
caller's registers (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev outer : Addr := s₀.gpr .rsi
abbrev op : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀, H.S⟩
abbrev outerR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outer s₀, H.S⟩
abbrev opR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.op s₀, H.D⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- Where the digests go. -/
abbrev T : Addr := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀ + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀]
  i_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀)
  i_p : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀)
  i_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀)
  o_p : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀)
  o_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀)
  p_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀)
  ret_i : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀)
  ret_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀)
  ret_p : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀)
  ret_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀)
  stk_i : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outerR (H := H) s₀)
  stk_p : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀)
  nw : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 256
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (VG.Proof.Pbkdf2.Md.X86_64.Calls.finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.tR (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.calR hH s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Stream.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.calR hH s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact off_disj0 (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 48) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.calR hH s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) (m := hH.Wb) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) (a := 8 * H.W) (m := 48) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

omit hp in
theorem stk_ret : (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega_nat)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀
  r12 : s.gpr .r12 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outer s₀
  r13 : s.gpr .r13 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.op s₀
  r15 : s.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀
  saved : VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint r) : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15,
    h.saved.frame H hf hs, (hf.readW (r := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

theorem KR.regs {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.call {s₀ s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s) {ws : List Region} (ha : VG.Proof.Pbkdf2.Md.X86_64.Calls.After s ws s')
    (hs : ∀ r ∈ ws ++ [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀], (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)).Disjoint r)
    (hr : ∀ r ∈ ws ++ [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀], (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀).Disjoint r) : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.rsp] at f
  exact h.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f hs hr

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H) sc s₀)
include hp

theorem wr_mem : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀ ∈ s₀.wr ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s ∧ s.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ ∧
    s.gpr .rdx = s₀.gpr .rdx ∧ Frame [VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)] s₀.mem s.mem := by
  have hL : 8 * H.W + 48 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine VG.Proof.Pbkdf2.Md.X86_64.Calls.save_ok H (scr := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) rfl hp.hW (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r15 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    k _ (by decide) (by decide) (by decide) (by decide),
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    hm ▸ sv₁, ?_⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩
  rw [hm]
  exact (f₁.readW (r := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)) (by decide))

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ t) (hdi : t.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀)
    (hdx : t.gpr .rdx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (hcx : t.gpr .rcx = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) :
    VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
  obtain ⟨sR, iR, _⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.wr_mem hp
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx
      cw := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.t_sub hp)
      st_sc := hp.i_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_sub hH hp)
      o_sc := (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_t hH hp).symm
      stk_st := by rw [hk.rsp]; exact hp.stk_i
      stk_o := by rw [hk.rsp]; exact hp.stk_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.t_sub hp)
      stk_sc := by rw [hk.rsp]; exact hp.stk_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_sub hH hp) }

/-- The first call's arguments: the count from `rdx`. -/
theorem fin1Args_ok {s : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s) (hdi : s.gpr .rdi = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) {c : BitVec 64}
    (hdx : s.gpr .rdx = c) :
    WP isa (.block ([] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
      ([.mov .rcx (.reg .r15)] : List Instr))) s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ t ∧
        VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem := by
  have hf := hp.fits; have hW := hp.hW; have hbuf : H.buf = 8 * H.W + 48 := rfl
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov fun s₄ u₄ _ _ =>
    WP.block_nil ?_
  have k₄ : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s₄ := hk.regs (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  refine ⟨k₄, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r15, VG.Proof.Pbkdf2.Md.X86_64.Calls.sx_ofNat (by omega_nat)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r15]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hdx]

/-- The second call's arguments: the state at `rbx`, of `B + D` bytes. -/

theorem finCall_ok {t : State} (hk : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ t) (ha : VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s' → Frame [VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.tR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.calR hH s₀, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.rsp] at f
    refine hQ s' (hk.call ha' ?_ ?_) f hpost
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)
      · exact VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_t hp
      · exact (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_save hH hp).symm
      · exact hp.stk_s.symm.sub_left (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.save_sub hp)
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.ret_i
      · exact hp.ret_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.t_sub hp)
      · exact hp.ret_s.sub_right (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.cal_sub hH hp)
      · exact (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.stk_ret (s₀ := s₀)).symm


end

/-! ## In two runs -/

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
    ([.mov .rcx (.reg .r15)] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H) sc s₀) (hp' : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.Pre (H := H) sc s₀') (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : VG.Proof.Pbkdf2.Md.X86_64.Calls.PubEq s₀ s₀') (h : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s) (h' : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀' s') :
    ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn, hq.rdi]
  · rw [h.r12, h'.r12, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outer, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.outer, hq.rsi]
  · rw [h.r13, h'.r13, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.op, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.op, hq.rcx]
  · rw [h.r15, h'.r15, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀' = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀ ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀' = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀ ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀' = VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀ :=
  ⟨hq.rdi.symm, by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀' t ∧
      VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀') (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀') (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀') ∧ t.gpr .rsi = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ s ∧ VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.eqs hq
  have ha := VG.Proof.Pbkdf2.Md.X86_64.Calls.rel_taint (G := fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀ t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) ∧
      t.gpr .rsi = c)
    (G' := fun t => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.KR (H := H) s₀' t ∧ VG.Proof.Pbkdf2.Md.X86_64.Calls.FinArgs hH t (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀) ∧ t.gpr .rsi = c)
    VG.Proof.Pbkdf2.Md.X86_64.HmacFin.kregs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
  refine ha.seq (VG.Proof.Pbkdf2.Md.X86_64.Calls.rel_wp (VG.Proof.Pbkdf2.Md.X86_64.Calls.fin_rel hH (st := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.inn s₀) (o := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.T (H := H) s₀) (sc := VG.Proof.Pbkdf2.Md.X86_64.HmacFin.scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => VG.Proof.Pbkdf2.Md.X86_64.HmacFin.finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: words

What `copy32` (`Impl/Pbkdf2/Md/X86_64.lean`) writes: 32-bit words copied from
one region to another; and facts about registers and regions the proofs share.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append write_eq_writeBytes)
open VG.Proof.Hmac.Common (copy_mem bytesAt_add bytesAt_writeBytes_sep bytesAt_zero bytesAt_length)
open Spec.Sha256 (bytesAt)

theorem ea_nat (s : State) (b : Reg) (o : Nat) : s.ea (at_ b o) = s.gpr b + BitVec.ofNat 64 o := by
  rw [ea_at, ofInt_natCast]

/-! ## Copies -/

/-- `copy32 src so dst d n` writes the `4 n` bytes at `src + so` to `dst + d`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (Hash.copy32 src o₁ dst o₂ n ++ rest)) s Q := by
  exact Pbkdf2.X86_64.copy32_ok hs hd o₁ o₂ n

/-! ## Registers and regions -/

theorem wp_mov32r {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem zx32 (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem contains_pre {b : Addr} {n k : Nat} (h : n ≤ k) : (⟨b, k⟩ : Region).Contains b n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

end VG.Proof.Pbkdf2.Md.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCommon`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s parts

The precondition of `pbkdf2` (`Pre`), the parts of its `scratch`, what every
piece of it keeps (`KR`), and the calls of the functions it calls: the hash
function's streaming functions (`VG.Proof.Pbkdf2.Md.X86_64.Calls.StreamOK`), HMAC's
`init` and `finalize`, and `iterate`, whose proofs it takes as hypotheses.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Sizes pbkG)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG After SavedRegs ne_rsp callEntry_bytes SavedRegs.frame)
open VG.Proof.Hmac.Generic.Common (bytes_keep sub_of_off sub_of_self)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .rdi
abbrev pwl : Nat := (s₀.gpr .rsi).toNat
abbrev salt : Addr := s₀.gpr .rdx
abbrev sl : Nat := (s₀.gpr .rcx).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r8).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .r9
abbrev ol : Nat := (stackArg s₀ 0).toNat
abbrev scr : Addr := stackArg s₀ 1
abbrev pwR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl s₀⟩
abbrev saltR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.sl s₀⟩
abbrev outR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol s₀⟩
abbrev scR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, (H.W + H.S) * 8⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - BitVec.ofNat 64 24, 24⟩
/-- An address in `scratch`, and a part of it. -/
abbrev A (o : Nat) : Addr := VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ o, n⟩
/-- Our caller's registers, `out` and `c - 1`. -/
abbrev hdrR : Region := VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ H.sv 64
/-- The working space of the functions we call. -/
abbrev lowR : Region := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, 8 * H.W⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  sp₁ : 24 ≤ (s₀.gpr .rsp).toNat
  sp₂ : (s₀.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s₀.rd = [VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀]
  wr : s₀.wr = [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀]
  pw_o : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀)
  pw_s : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)
  sa_o : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀)
  sa_s : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)
  o_s : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)
  o_a : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀)
  s_a : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀)
  ret_pw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwR s₀)
  ret_sa : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltR s₀)
  ret_o : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀)
  ret_s : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)
  ret_a : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀)
  stk_pw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwR s₀)
  stk_sa : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.saltR s₀)
  stk_o : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀)
  stk_s : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀)
  stk_a : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀)
  pwnw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw s₀).toNat + VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl s₀ ≤ 2 ^ 64
  sanw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt s₀).toNat + VG.Proof.Pbkdf2.Md.X86_64.Pbk.sl s₀ ≤ 2 ^ 64
  onw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀).toNat + VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol s₀ ≤ 2 ^ 64
  snw : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀).toNat + (H.W + H.S) * 8 ≤ 2 ^ 64
  c0 : 0 < VG.Proof.Pbkdf2.Md.X86_64.Pbk.cc s₀
  olD : VG.Proof.Pbkdf2.Md.X86_64.Pbk.ol s₀ ≤ (2 ^ 32 - 1) * H.D

theorem pre_of (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H) {s₀ : State} (h : (VG.Proof.Pbkdf2.Md.X86_64.pbkG hH.SH (H.W + H.S)).pre s₀) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  have hD := hH.hD
  simp only [hD] at h26
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

/-- The sizes, as facts about natural numbers. -/
structure PSizes (H : Hash) : Prop where
  z : VG.Proof.Pbkdf2.Md.X86_64.Sizes H
  W : H.W ≤ 256

theorem _root_.VG.Proof.Pbkdf2.Md.X86_64.HashOK.psizes (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H) : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H := ⟨hH.sizes, hH.hW⟩

/-! ## The parts of `scratch` -/

/-- Where the parts of `scratch` are. -/
theorem layout : H.sv = 8 * H.W ∧ H.outO = 8 * H.W + 48 ∧ H.cO = 8 * H.W + 56 ∧ H.st0O = 8 * H.W + 64 ∧
    H.st1O = 8 * H.W + 64 + H.S ∧ H.stSO = 8 * H.W + 64 + 2 * H.S ∧ H.stWO = 8 * H.W + 64 + 3 * H.S ∧
    H.uO = 8 * H.W + 64 + 4 * H.S ∧ H.tO = 8 * H.W + 64 + 4 * H.S + H.D ∧
    H.hkO = 8 * H.W + 64 + 4 * H.S + 2 * H.D ∧ H.intO = 8 * H.W + 64 + 4 * H.S + 2 * H.D + H.P.N ∧
    H.S = H.P.N + H.P.B := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [Hash.sv, Hash.st0O, Hash.st1O, Hash.stSO, Hash.stWO, Hash.uO, Hash.tO,
      Hash.hkO, Hash.intO] <;> omega

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H)

include hz in
/-- The parts of `scratch`, as offsets: they end before its end. -/
theorem end_le : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  have := hz.z.N; have := hz.z.D; have := hz.z.B; have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.layout (H := H)
  omega

include hz in
theorem L_lt : (H.W + H.S) * 8 < 2 ^ 64 := by
  have := hz.W; have := hz.z.N; have := hz.z.B_le; show (H.W + (H.P.N + H.P.B)) * 8 < 2 ^ 64; omega

theorem part_sub {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ o n) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀) :=
  Offset.sub_base _ h

include hz in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ (H.W + H.S) * 8)
    (hb : b + n ≤ (H.W + H.S) * 8) : Region.Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ a m) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ b n) := by
  have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.L_lt hz; exact Offset.disjoint _ h (by omega) (by omega)

include hz in
theorem low_disj {b n : Nat} (hb : 8 * H.W ≤ b) (hbn : b + n ≤ (H.W + H.S) * 8) :
    Region.Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ b n) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lowR (H := H) s₀) := by
  have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.L_lt hz; exact Offset.disjoint_base _ hb (by omega)

theorem low_sub : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Pbk.lowR (H := H) s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀) :=
  Region.sub_prefix (by show 8 * H.W ≤ (H.W + H.S) * 8; omega)

include hp hz in
theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ (H.W + H.S) * 8) :
    InRegions s.wr (VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ o) n := by
  have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.L_lt hz
  exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega)⟩

include hp in
theorem sc_mem : VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem stk_ret : (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀).Disjoint (VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by omega) x h₂ h₁

/-- The 8 · (depth + 1) bytes below `rsp` that a call of depth at most 2 uses. -/
theorem below_stk {n : Nat} (hn : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀) :=
  below_sub hn (by omega)

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the entry on: our caller's registers,
`out` and `c - 1` in `scratch`, and everything written is in `out`,
`scratch` or the stack. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀
  saved : VG.Proof.Pbkdf2.Md.X86_64.Calls.SavedRegs H.hh (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀) s₀ s.mem
  outW : s.mem.readW (VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ H.outO) 64 = VG.Proof.Pbkdf2.Md.X86_64.Pbk.out s₀
  cW : s.mem.readW (VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ H.cO) 64 = BitVec.ofNat 64 (VG.Proof.Pbkdf2.Md.X86_64.Pbk.cc s₀ - 1)
  frame : Frame [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀] s₀.mem s.mem

/-- Registers `KR` fixes. -/
abbrev kregs : List Reg := [.r15, .rsp]

theorem hdr_sub {s₀ : State} {o : Nat} (h₁ : H.sv ≤ o) (h₂ : o + 8 ≤ H.sv + 64) :
    Region.Sub ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ o, 8⟩ (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hdrR (H := H) s₀) := Offset.sub _ h₁ h₂

section
variable {s₀ : State} (hp : VG.Proof.Pbkdf2.Md.X86_64.Pbk.Pre (H := H) s₀) (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H)
include hp hz

omit hp hz in
theorem KR.keep {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hdrR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀], Region.Sub r r') :
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s' := by
  have hs : Region.Sub (VG.Proof.Pbkdf2.Md.X86_64.Calls.saveR H.hh (VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀)) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hdrR (H := H) s₀) := Offset.sub _ (Nat.le_refl _) (by
    show 8 * H.W + 48 ≤ 8 * H.W + 64; omega)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, h15.trans h.r15,
    SavedRegs.frame H.hh h.saved hf fun r hr => (hd r hr).sub_left hs, ?_, ?_, h.frame.trans (hf.sub hsub)⟩
  · rw [← h.outW]
    exact hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ H.outO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hdr_sub (by simp [Hash.outO]) (by simp [Hash.outO])))
      (by decide)
  · rw [← h.cW]
    exact hf.readW (r := ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.A s₀ H.cO, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.hdr_sub (by simp [Hash.cO]) (by simp [Hash.cO])))
      (by decide)

omit hp in
/-- A write into a part of `scratch` after its header keeps `KR`. -/
theorem KR.write {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (h15 : s'.gpr .r15 = s.gpr .r15) {o n : Nat}
    (ho : H.st0O ≤ o) (hon : o + n ≤ (H.W + H.S) * 8) (hf : Frame [VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ o n] s.mem s'.mem) :
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp h15 hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.part_disj hz (Or.inl (by simpa [Hash.st0O] using ho)) (by
        have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.end_le hz; simp only [Hash.st0O] at ho; omega) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.X86_64.Pbk.part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after its header, or its
working space, and the stack below `rsp`. -/
theorem KR.call {s s' : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {ws : List Region} {n : Nat} (hn : n ≤ 24)
    (hf : Frame (ws ++ [below (s.gpr .rsp) n]) s.mem s'.mem)
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = VG.Proof.Pbkdf2.Md.X86_64.Pbk.sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) :
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s' := by
  have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.end_le hz; have := VG.Proof.Pbkdf2.Md.X86_64.Pbk.layout (H := H)
  have hst : H.sv + 64 = H.st0O := by simp [Hash.st0O]
  refine h.keep hrd hwr (hcs _ (by simp [calleeSaved])) (hcs _ (by simp [calleeSaved])) hf
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact (VG.Proof.Pbkdf2.Md.X86_64.Pbk.low_disj hz (Nat.le_refl _) (by omega)).sub_right (Region.sub_prefix hk)
      · exact VG.Proof.Pbkdf2.Md.X86_64.Pbk.part_disj hz (Or.inl (by rw [hst]; exact h₁)) (by rw [hst]; omega) h₂
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ((hp.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.below_stk hn)).sub_right (VG.Proof.Pbkdf2.Md.X86_64.Pbk.part_sub (by rw [hst]; omega))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
      · exact ⟨VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, by simp, Region.sub_prefix (by show k ≤ (H.W + H.S) * 8; omega)⟩
      · exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.X86_64.Pbk.part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h.rsp]
      exact ⟨_, by simp, VG.Proof.Pbkdf2.Md.X86_64.Pbk.below_stk hn⟩

omit hp hz in
/-- The regions only read are the same as on entry. -/
theorem KR.bytes {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀], Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep h.frame hd hn

omit hz in
theorem KR.pwBytes {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) :
    bytesAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl s₀) = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pw s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.pwl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.stk_pw.symm) (by have := hp.pwnw; omega)

omit hz in
theorem KR.saltBytes {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) :
    bytesAt s.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sl s₀) = bytesAt s₀.mem (VG.Proof.Pbkdf2.Md.X86_64.Pbk.salt s₀) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.sl s₀) :=
  h.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.stk_sa.symm) (by have := hp.sanw; omega)

omit hp hz in
theorem KR.readW {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) {R : Region} {a : Addr} (hc : R.Contains a 8)
    (hd : ∀ r ∈ [VG.Proof.Pbkdf2.Md.X86_64.Pbk.outR s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.scR (H := H) s₀, VG.Proof.Pbkdf2.Md.X86_64.Pbk.stkR s₀], R.Disjoint r) :
    s.mem.readW a 64 = s₀.mem.readW a 64 :=
  h.frame.readW hc hd (by decide)

omit hz in
theorem KR.ret {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
  h.readW (R := VG.Proof.Pbkdf2.Md.X86_64.Pbk.retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s
    · exact stk_ret.symm)

omit hz in
/-- `out_len`, on the stack. -/
theorem KR.olW {s : State} (h : VG.Proof.Pbkdf2.Md.X86_64.Pbk.KR (H := H) s₀ s) :
    s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 :=
  h.readW (R := VG.Proof.Pbkdf2.Md.X86_64.Pbk.argR s₀) (VG.Proof.Pbkdf2.Md.X86_64.contains_pre (by decide)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.stk_a.symm)

end

/-! ## Facts about the offsets

Each proved once, by `omega` on `layout`, for the step proofs: an `omega`
over a step's context, which holds many facts about states and sizes, costs
far more. -/

theorem PSizes.B_ge (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 64 ≤ H.P.B := by rcases hz.z.B with h | h <;> omega
theorem PSizes.o_0_lt_S (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 0 < H.S := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_B_1_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B + 1 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_B_1_lt_p64 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B + 1 < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_B_4_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B + 4 < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_B_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_B_lt_p32 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_D_le_p64 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.D ≤ 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.D < 2 ^ 31 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_p32 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.D < 2 ^ 32 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_D_lt_p64 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.D < 2 ^ 64 := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_S_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.S < 2 ^ 31 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_W8_48_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_W8_48_le_outO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W + 48 ≤ H.outO := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_W8_le_hkO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_intO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_st0O (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_st1O (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_stSO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_sv (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.sv := by
  simp only [Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_tO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_W8_le_uO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : 8 * H.W ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_cO_64d8_le_outO_16 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.cO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega
theorem PSizes.o_cO_8_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.cO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.cO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_hkO_D_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.hkO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_hkO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.hkO < 2 ^ 31 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_intO_4_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.intO + 4 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_intO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.intO < 2 ^ 31 := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_outO_16_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO + 16 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_outO_16_lt_p64 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO + 16 < 2 ^ 64 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_outO_64d8_le_outO_16 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO + 64 / 8 ≤ H.outO + 16 := by
  simp only [Hash.outO, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N4; omega
theorem PSizes.o_outO_8_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO + 8 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.outO, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_outO_8_le_cO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO + 8 ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_outO_le_cO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.outO ≤ H.cO := by
  simp only [Hash.cO, Hash.outO, Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_2mS_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + 2 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_st0O_2mS_le_tO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + 2 * H.S ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_3mS_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + 3 * H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_st0O_S_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_st0O_S_le_hkO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_S_le_st1O (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_S_le_stSO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_le_st0O (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O ≤ H.st0O := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_le_st1O (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O ≤ H.st1O := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_le_stSO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O < 2 ^ 31 := by
  simp only [Hash.st0O, Hash.sv]; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_st1O_S_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_st1O_S_le_hkO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st1O_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st1O_S_le_stSO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ H.stSO := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st1O_S_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st1O_S_le_uO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st1O_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st1O < 2 ^ 31 := by
  simp only [Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_stSO_S_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stSO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_stSO_S_le_st0O_3mS (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stSO + H.S ≤ H.st0O + 3 * H.S := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stSO_S_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stSO + H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stSO_hsS_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stSO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stSO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stSO < 2 ^ 31 := by
  simp only [Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_stWO_S_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_stWO_S_le_intO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stWO_S_le_uO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.S ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stWO_hsS_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ (H.W + H.S) * 8 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_hsS_le_hkO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_hsS_le_intO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO + H.stream.S ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have : H.stream.S = H.P.N + H.P.B := rfl; omega
theorem PSizes.o_stWO_le_intO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO ≤ H.intO := by
  simp only [Hash.intO, Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stWO_le_tO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_stWO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO < 2 ^ 31 := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_sv_64_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.sv + 64 ≤ (H.W + H.S) * 8 := by
  simp only [Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_tO_D_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.tO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_tO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.tO < 2 ^ 31 := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_uO_D_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.uO + H.D ≤ (H.W + H.S) * 8 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_uO_D_le_tO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.uO + H.D ≤ H.tO := by
  simp only [Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_uO_lt_p31 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.uO < 2 ^ 31 := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; omega
theorem PSizes.o_so_48_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.so + 48 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; have := hz.z.fits; omega
theorem PSizes.o_so_48_le_W8 (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.so + 48 ≤ 8 * H.W := by
  have := hz.z.D.2.1; have := hz.z.fits; omega
theorem PSizes.o_stWO_le_uO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.stWO ≤ H.uO := by
  simp only [Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_S_eq_st1O (_hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + H.S = H.st1O := rfl
theorem PSizes.o_st0O_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_hkO_N_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.hkO + H.P.N ≤ (H.W + H.S) * 8 := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_st0O_le_hkO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O ≤ H.hkO := by
  simp only [Hash.hkO, Hash.tO, Hash.uO, Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_D_le_B (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.D ≤ H.P.B := by
  have := hz.z.D.2.1; have := hz.z.N.2; have := hz.z.B_le; have := hz.W; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega
theorem PSizes.o_sv_64_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.sv + 64 ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_st0O_3mS_le_stWO (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.st0O + 3 * H.S ≤ H.stWO := by
  simp only [Hash.stWO, Hash.stSO, Hash.st1O, Hash.st0O, Hash.sv]; have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; omega
theorem PSizes.o_B_5_le_L (hz : VG.Proof.Pbkdf2.Md.X86_64.Pbk.PSizes H) : H.P.B + 5 ≤ (H.W + H.S) * 8 := by
  have : H.S = H.P.N + H.P.B := rfl; have := hz.z.D.2.1; have := hz.z.N.1; have := hz.B_ge; have := hz.z.D.1; omega

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls`. -/
section

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s calls

The calls of HMAC's `init` and `finalize` and of `iterate`, whose contracts
(`initG`, `finG`, `iterK`) their proofs are given as hypotheses: each is run
with `WP.call`, and shown constant time in two runs with `RelCT.call`. Each
uses at most 24 bytes of stack below `rsp` (a call two deep).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG ne_rsp callEntry_bytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : VG.Proof.Pbkdf2.Md.X86_64.HashOK H)

theorem ret24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega) (by omega)

theorem stk24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 16, 16⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 16 = s.gpr .rsp - BitVec.ofNat 64 24 from
    Offset.sub_sub_ofNat _ 8 16]
  exact Offset.sub_below _ (a := 24) (by omega) (by omega)

theorem stk8 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 8 = s.gpr .rsp - BitVec.ofNat 64 16 from
    Offset.sub_sub_ofNat _ 8 8]
  exact Offset.sub_below _ (a := 16) (by omega) (by omega)

theorem b16 (s : State) : Region.Sub (below (s.gpr .rsp) 16) (below (s.gpr .rsp) 24) :=
  below_sub (by omega) (by omega)

/-- The bytes of a region outside the 24 bytes below `rsp` read the same on
entry to a callee. -/
theorem entry_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => VG.Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s (hd.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.b16 s)) hn (List.mem_range.mp hi)

/-- A streaming state outside the 24 bytes below `rsp` represents the same
message on entry to a callee. -/
theorem entry_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, H.S⟩) {m : List Byte}
    (h : hH.SH.Repr s.mem p m) : hH.SH.Repr s.callEntry.mem p m :=
  hH.stream.repr _ _ _ _ _ (fun i hi => VG.Proof.Pbkdf2.Md.X86_64.Calls.callEntry_bytes s (hd.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.b16 s))
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) h

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = out
  rdx : s.gpr .rdx = k
  rcx : (s.gpr .rcx).toNat = kl
  r8 : s.gpr .r8 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨out, H.S⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨k, kl⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := H) s inn out k sc kl) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hB := hH.hB
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, a.r8, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s,
    a.stk_i.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s),
    a.stk_i.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.stk_k.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s),
    a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.scnw⟩

theorem hinit_call (hv : Verified X86_64.target H.hmacInit (VG.Proof.Pbkdf2.Md.X86_64.Calls.initG hH.SH H.W)) (hsp : NoSp H.hmacInit)
    (hd : H.hmacInit.depth ≤ 2) {s : State} {inn out k sc : Addr} {kl : Nat}
    (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  have e : bytesAt s.callEntry.mem k kl = bytesAt s.mem k kl :=
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_bytes s a.stk_k (by have := a.klB; have := hH.B_le; omega)
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.initG, State.withRegions_gpr, State.withRegions_mem, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, e] at hpost
  exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) hpost.1 hpost.2

theorem hinit_rel (hv : Verified X86_64.target H.hmacInit (VG.Proof.Pbkdf2.Md.X86_64.Calls.initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := H) s inn out k sc kl ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.InitArgs (H := H) s' inn out k sc kl ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.initG, State.withRegions_gpr, State.callEntry_rsp, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.r8, a'.r8, cx, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = outer
  rdx : s.gpr .rdx = cnt
  rcx : s.gpr .rcx = o
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨outer, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨o, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := H) s inn outer cnt o sc) :
    (VG.Proof.Pbkdf2.Md.X86_64.Calls.finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s,
    a.stk_i.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_u.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s),
    a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_i.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.stk_u.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s),
    a.stk_o.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk24 s), a.scnw⟩

theorem hfin_call (hv : Verified X86_64.target H.hmacFin (VG.Proof.Pbkdf2.Md.X86_64.Calls.finG hH.SH H.W)) (hsp : NoSp H.hmacFin)
    (hd : H.hmacFin.depth ≤ 2) {s : State} {inn outer cnt o sc : Addr}
    (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) fun k0 text hk hl hi hc ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finG, State.withRegions_gpr, State.withRegions_mem, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB] at hpost
  exact hpost k0 text hk hl (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_repr hH s a.stk_i hi) hc (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_repr hH s a.stk_u ho)

theorem hfin_rel (hv : Verified X86_64.target H.hmacFin (VG.Proof.Pbkdf2.Md.X86_64.Calls.finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := H) s inn outer cnt o sc ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.FinArgs (H := H) s' inn outer cnt o sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [VG.Proof.Pbkdf2.Md.X86_64.Calls.finG, State.withRegions_gpr, State.callEntry_rsp, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  rdi : s.gpr .rdi = key
  rsi : s.gpr .rsi = u
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = t
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨key, 2 * H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨u, H.D⟩
  stk_t : (below (s.gpr .rsp) 24).Disjoint ⟨t, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.IterArgs (H := H) s key u n t sc) :
    (iterK hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s,
    a.stk_k.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_u.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_t.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s),
    a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.ret24 s), a.stk_k.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk8 s), a.stk_u.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk8 s),
    a.stk_t.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk8 s), a.stk_s.sub_left (VG.Proof.Pbkdf2.Md.X86_64.Pbk.stk8 s), a.knw, a.scnw⟩

theorem iter_call (hv : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hsp : NoSp H.iterate)
    (hd : H.iterate.depth ≤ 2) {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : VG.Proof.Pbkdf2.Md.X86_64.Pbk.IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) fun k0 hk hi ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  have hS2 : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  have hDn : H.D ≤ 2 ^ 64 := by have := hH.hDN; have := hH.N_le; omega
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB, hS,
    VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_bytes s a.stk_u hDn, VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_bytes s a.stk_t hDn] at hpost
  have eS : H.S = H.P.N + H.P.B := rfl
  refine hpost k0 hk (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_repr hH s (a.stk_k.sub_right (Region.sub_prefix (by omega))) hi)
    (VG.Proof.Pbkdf2.Md.X86_64.Pbk.entry_repr hH s (a.stk_k.sub_right (Offset.sub_base _ (by omega))) ho)

theorem iter_rel (hv : Verified X86_64.target H.iterate (iterK hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → VG.Proof.Pbkdf2.Md.X86_64.Pbk.IterArgs (H := H) s key u n t sc ∧ VG.Proof.Pbkdf2.Md.X86_64.Pbk.IterArgs (H := H) s' key u n t sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a.cr a.cw, a.cw, VG.Proof.Pbkdf2.Md.X86_64.Pbk.covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [iterK, State.withRegions_gpr, State.callEntry_rsp, VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rsi ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.rcx ≠ .rsp), VG.Proof.Pbkdf2.Md.X86_64.Calls.ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.X86_64.Pbk

end
