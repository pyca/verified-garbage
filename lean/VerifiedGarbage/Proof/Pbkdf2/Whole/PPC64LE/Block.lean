module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.PPC64LE
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Contract
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Save
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-! ### `Pbkdf2.Whole.PPC64LE.Setup`, which only this module used -/

section

/-! ### `Pbkdf2.Whole.PPC64LE.Calls`, which only this module used -/

section

/-! ### `Pbkdf2.Whole.PPC64LE.Common`, which only this module used -/

section

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the layout

What the proofs need of the functions `pbkdf2` calls (`FnsOK`): the facts
about the streaming functions (`HashOK`), HMAC's `init` against its shared
contract with `X + 96` bytes of stack, and the constant time of HMAC's
`finalize` and of `iterate`. `Pre` is `pbkdf2`'s precondition; the parts of
`scratch` (`sR`) are within it and apart from each other (`part_sub`,
`part_disj`); `KR` is what holds from the start of the frame on: the
regions, the stack pointer, the registers holding the arguments, our
caller's registers in the save area, and memory outside `out`, `scratch` and
the stack below the stack pointer (`stk`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK finG Saved untouched untouched_pres saved_keep)
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)
open Spec.Sha256 (bytesAt)

/-- HMAC's `init` for a key of any length, with `X + 96` bytes of stack. -/
abbrev hiK (SH : Spec.Hmac.StreamingHash) (X : Nat) : Contract isa :=
  Spec.Hmac.initAnyKeyContract SH PPC64LE.abi (X + 96)

/-- The facts about the functions `pbkdf2` calls. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  /-- The bytes of stack HMAC's `init` uses beyond those of its callees. -/
  X : Nat
  hi : ∀ s, (hiK hH.SH X).pre s → ∃ t s', Exec isa F.hiC s t s' ∧ abiPreserved s s' ∧ (hiK hH.SH X).post s s'
  hiCt : ConstantTime isa (hiK hH.SH X).pre (hiK hH.SH X).pub F.hiC
  hiSd : sdepth F.hiC ≤ X + 96
  hfCt : ConstantTime isa (finG hH.SH (F.H.W + 48 + F.H.FD) 96).pre (finG hH.SH (F.H.W + 48 + F.H.FD) 96).pub
    F.H.finalize
  /-- `iterate`, correct and constant time with `itW` bytes of working space
  and 96 bytes of stack, in at most two nested frames. -/
  itOk : ∀ s, (iterG hH.SH F.itW 96).pre s →
    ∃ t s', Exec isa F.itC s t s' ∧ abiPreserved s s' ∧ (iterG hH.SH F.itW 96).post s s'
  itCt : ConstantTime isa (iterG hH.SH F.itW 96).pre (iterG hH.SH F.itW 96).pub F.itC
  itFd : F.itC.fdepth ≤ 2
  itPf : pushFrames F.itC = true
  /-- The working space of every function we call fits in `Wc` bytes. -/
  hWc : F.H.W + 48 + F.H.S + F.H.FD + F.H.FD ≤ F.Wc
  hIt : F.itW ≤ F.Wc
  hX : X ≤ 4096
  reach : F.bytes ≤ 4096

/-! ## The arguments and the regions -/

section
variable (F : Fns) (X : Nat) (s₀ : State)

abbrev pw : Addr := s₀.gpr .r3
abbrev pwl : Nat := (s₀.gpr .r4).toNat
abbrev salt : Addr := s₀.gpr .r5
abbrev sl : Nat := (s₀.gpr .r6).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r7).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .r8
abbrev ol : Nat := (s₀.gpr .r9).toNat
abbrev scr : Addr := s₀.gpr .r10
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
abbrev scR : Region := ⟨scr s₀, F.bytes⟩
/-- The stack below the stack pointer the code and its callees use. -/
abbrev stk : Region := below s₀.sp (X + 144)
/-- An address in `scratch`, and a part of it. -/
abbrev sA (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨sA s₀ o, n⟩
/-- Everything the code writes. -/
abbrev wrs : List Region := [outR s₀, scR F s₀, stk X s₀]

end

/-- The precondition. -/
structure Pre (F : Fns) (X : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀]
  wr : s₀.wr = [outR s₀, scR F s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR F s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR F s₀)
  o_s : (outR s₀).Disjoint (scR F s₀)
  sp : X + 144 ≤ s₀.sp.toNat
  b_pw : (stk X s₀).Disjoint (pwR s₀)
  b_sa : (stk X s₀).Disjoint (saltR s₀)
  b_o : (stk X s₀).Disjoint (outR s₀)
  b_s : (stk X s₀).Disjoint (scR F s₀)
  npw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  nsa : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  no : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  nsc : (scr s₀).toNat + F.bytes ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

theorem pre_of {F : Fns} (hF : FnsOK F) {s₀ : State}
    (h : (pbkG hF.hH.SH F.bytes (hF.X + 144)).pre s₀) : Pre F hF.X s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  rw [hF.hH.hD] at h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

/-! ## The layout of `scratch` -/

section
variable {F : Fns}

/-- Where the parts of `scratch` are. -/
theorem layout : F.st0O = 48 + F.Wc ∧ F.st1O = 48 + F.Wc + F.H.S ∧
    F.stWO = 48 + F.Wc + 2 * F.H.S ∧ F.uO = 48 + F.Wc + 3 * F.H.S ∧
    F.tO = 48 + F.Wc + 3 * F.H.S + F.H.D ∧ F.intO = 48 + F.Wc + 3 * F.H.S + 2 * F.H.D ∧
    F.bytes = 48 + F.Wc + 3 * F.H.S + 2 * F.H.D + 4 := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stWO, Fns.uO, Fns.tO, Fns.intO, Fns.bytes, Fns.cO]
  omega_using []

variable (hF : FnsOK F)
include hF

/-- The sizes the proofs use. -/
structure Sz (F : Fns) : Prop where
  N : 0 < F.H.N ∧ F.H.N ≤ 64
  B : F.H.B = 64 ∨ F.H.B = 128
  S : F.H.S = F.H.N + F.H.B
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.FD ∧ F.H.FD ≤ 64 ∧ F.H.D ≤ F.H.B
  D4 : F.H.D % 4 = 0
  N4 : F.H.N % 4 = 0
  W : F.H.W ≤ 1024
  Wc : F.H.W + 48 + F.H.S + F.H.FD + F.H.FD ≤ F.Wc
  reach : F.bytes ≤ 4096

theorem sizes : Sz F := by
  obtain hN := hF.hH.dims.N; have hB := hF.hH.dims.B; have hW := hF.hH.dims.so
  have hb := hF.hWc
  exact ⟨hN, hB, rfl, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hFD64, hF.hH.hDB⟩, hF.hH.hD4, hF.hH.hN4, hW.2, hb, hF.reach⟩

end

section
variable {F : Fns} {X : Nat} {s₀ : State} (hp : Pre F X s₀)
include hp

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ F.bytes) : Region.Sub (sR s₀ o n) (scR F s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj (hr : F.bytes ≤ 4096) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.bytes)
    (hb : b + n ≤ F.bytes) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) :=
  Offset.disjoint _ h (by omega_using [hr, ha]) (by omega_using [hr, hb])

omit hp in
theorem part_contains (hr : F.bytes ≤ 4096) {o n : Nat} (h : o + n ≤ F.bytes) :
    (scR F s₀).Contains (sA s₀ o) n :=
  Offset.contains_base _ h (by omega_using [hr, h])

theorem sc_wr {s : State} (hwr : s.wr = s₀.wr) : scR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem out_wr {s : State} (hwr : s.wr = s₀.wr) : outR s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem in_sc (hr : F.bytes ≤ 4096) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.bytes) :
    InRegions s.wr (sA s₀ o) n :=
  ⟨_, sc_wr hp hwr, part_contains (s₀ := s₀) hr h⟩

theorem in_sc' (hr : F.bytes ≤ 4096) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.bytes) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (sc_wr hp hwr), part_contains (s₀ := s₀) hr h⟩

/-- The stack below the stack pointer of the frame. -/
theorem below_stk {n : Nat} (hn : n + 48 ≤ X + 144) : Region.Sub (below (s₀.sp - 48) n) (stk X s₀) :=
  fun x hx => below_sub hn (by have := hp.sp; have := s₀.sp.isLt; omega_arith) x (below_body s₀.sp n x hx)

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the start of the frame on. -/
structure KR (F : Fns) (X : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp - 48
  r20 : s.gpr .r20 = s₀.gpr .r6
  r21 : s.gpr .r21 = scr s₀
  r22 : s.gpr .r22 = s₀.gpr .r7
  r25 : s.gpr .r25 = salt s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : Saved 0 (scr s₀) s₀.gpr s.mem
  frame : Frame (wrs F X s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r20, .r21, .r22, .r25, .r2, .r14, .r15, .r16, .r17, .r18, .r19, .r26, .r27, .r28,
  .r29, .r30, .r31]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

section
variable {F : Fns} {X : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR F X s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 0, 48⟩ r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F X s₀, Region.Sub r r') : KR F X s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r20, (hg _ (by simp)).trans h.r21,
    (hg _ (by simp)).trans h.r22, (hg _ (by simp)).trans h.r25,
    fun r hr => (hg r (by revert r; decide)).trans (h.un r hr), saved_keep h.saved hf hs,
    h.frame.trans (hf.sub hsub)⟩

/-- A part of `scratch` after the save area, or the stack below the frame. -/
def Wk (F : Fns) (X : Nat) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 48 ≤ o ∧ o + n ≤ F.bytes) ∨ ∃ n, r = below (s₀.sp - 48) n ∧ n + 48 ≤ X + 144

theorem Wk.ok (hp : Pre F X s₀) (hr : F.bytes ≤ 4096) {r : Region} (h : Wk F X s₀ r) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 0, 48⟩ r ∧ ∃ r' ∈ wrs F X s₀, Region.Sub r r' := by
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) hr (.inl h₁) (by omega_using [h₁, h₂]) h₂, _, by simp, part_sub (s₀ := s₀) h₂⟩
  · exact ⟨((hp.b_s.sub_left (below_stk hp hn)).sub_right (part_sub (s₀ := s₀) (o := 0) (n := 48) (by
      have := hr; simp only [Fns.bytes, Fns.intO, Fns.tO, Fns.uO, Fns.stWO, Fns.st1O, Fns.st0O,
        Fns.cO]; omega_using []))).symm, _, by simp, below_stk hp hn⟩

/-- What a call leaves, writing parts of `scratch` after the save area and
the stack below the frame. -/
theorem KR.call (hp : Pre F X s₀) (hb : F.bytes ≤ 4096) {s s' : State} (h : KR F X s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hw : ∀ r ∈ rs, Wk F X s₀ r) : KR F X s₀ s' :=
  h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr)) hf (fun r hr => (Wk.ok hp hb (hw r hr)).1)
    (fun r hr => (Wk.ok hp hb (hw r hr)).2)

/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F X s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs F X s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem KR.pwBytes (hp : Pre F X s₀) {s : State} (hk : KR F X s₀ s) :
    bytesAt s.mem (pw s₀) (pwl s₀) = bytesAt s₀.mem (pw s₀) (pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by show (s₀.gpr .r4).toNat ≤ 2 ^ 64; have := (s₀.gpr .r4).isLt; omega_using [])

theorem KR.saltBytes (hp : Pre F X s₀) {s : State} (hk : KR F X s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by show (s₀.gpr .r6).toNat ≤ 2 ^ 64; have := (s₀.gpr .r6).isLt; omega_using [])

end

end VG.Proof.Pbkdf2.Whole.PPC64LE

end

end


/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the calls

The calls of HMAC's `init` (against its shared contract, `WP.callAny`, since
it allocates its working space on the stack), of HMAC's `finalize` and of
`iterate` (against the contracts of their generic proofs, `WP.callF`): what
each needs of the state it is called from, and what holds when it returns.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK finG)
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns} (hF : FnsOK F)

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers, and memory outside `ws`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame ws s.mem s'.mem

/-! ## HMAC's `init` -/

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (hF : FnsOK F) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  h3 : s.gpr .r3 = inn
  h4 : s.gpr .r4 = ou
  h5 : s.gpr .r5 = k
  h6 : (s.gpr .r6).toNat = kl
  sp : hF.X + 96 ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_ik : Region.Disjoint ⟨inn, F.H.S⟩ ⟨k, kl⟩
  d_ok : Region.Disjoint ⟨ou, F.H.S⟩ ⟨k, kl⟩
  b_i : (below s.sp (hF.X + 96)).Disjoint ⟨inn, F.H.S⟩
  b_o : (below s.sp (hF.X + 96)).Disjoint ⟨ou, F.H.S⟩
  b_k : (below s.sp (hF.X + 96)).Disjoint ⟨k, kl⟩
  n_i : inn.toNat + F.H.S ≤ 2 ^ 64
  n_o : ou.toNat + F.H.S ≤ 2 ^ 64
  n_k : k.toNat + kl ≤ 2 ^ 64
  hc : Covers ([⟨k, kl⟩] ++ [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] s.wr

theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs hF s inn ou k kl) :
    (hiK hF.hH.SH hF.X).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) := by
  have hS := hF.hH.hS
  sig_pre [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [show hF.X + 95 + 1 = hF.X + 96 from rfl]
  simp only [h.h3, h.h4, h.h5, h.h6, hS]
  exact ⟨h.sp, trivial, trivial, h.d_io, h.d_ik, h.d_ok, h.b_i, h.b_o, h.b_k, h.n_i, h.n_o, h.n_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs hF s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] ++ [below s.sp (hF.X + 96)]) s' →
      hF.hH.SH.Repr s'.mem inn (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hF.hH.SH.Repr s'.mem ou (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa F.callHi s Q := by
  have hS := hF.hH.hS
  refine WP.callAny (k := hiK hF.hH.SH hF.X) hF.hi (rd := [⟨k, kl⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) h.pre (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := hF.hiSd; have := hF.hX; omega_arith)
  intro s' hrd hwr hsp' hf hcs hpost
  sig_post [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.initPost, PPC64LE.abi,
    PPC64LE.argRegs] at hpost
  simp only [h.h3, h.h4, h.h5, h.h6] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf hF.hiSd (by have := hF.hX; omega_arith)

/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {P : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs hF s inn ou k kl ∧ HiArgs hF s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa P F.callHi fun _ _ => True := by
  have hS := hF.hH.hS
  refine RelCT.call hF.hi hF.hiCt [⟨k, kl⟩] [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre, a'.pre, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  sig_pub [Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨e, a.h3.trans a'.h3.symm, a.h4.trans a'.h4.symm, a.h5.trans a'.h5.symm,
    BitVec.eq_of_toNat_eq (a.h6.trans a'.h6.symm)⟩

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou`, `out` at `o` and the working space at `sc`. -/
structure HfArgs (F : Fns) (s : State) (inn ou o sc : Addr) : Prop where
  h3 : s.gpr .r3 = inn
  h4 : s.gpr .r4 = ou
  h6 : s.gpr .r6 = o
  h7 : s.gpr .r7 = sc
  sp : 96 ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨o, F.H.D⟩
  d_is : Region.Disjoint ⟨inn, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  d_uo : Region.Disjoint ⟨ou, F.H.S⟩ ⟨o, F.H.D⟩
  d_us : Region.Disjoint ⟨ou, F.H.S⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  d_os : Region.Disjoint ⟨o, F.H.D⟩ ⟨sc, F.H.W + 48 + F.H.FD⟩
  b_i : (below s.sp 96).Disjoint ⟨inn, F.H.S⟩
  b_u : (below s.sp 96).Disjoint ⟨ou, F.H.S⟩
  b_o : (below s.sp 96).Disjoint ⟨o, F.H.D⟩
  b_s : (below s.sp 96).Disjoint ⟨sc, F.H.W + 48 + F.H.FD⟩
  hc : Covers ([⟨ou, F.H.S⟩] ++ [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] s.wr

theorem HfArgs.pre {s : State} {inn ou o sc : Addr} (h : HfArgs F s inn ou o sc) :
    (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).pre (s.callEntry.withRegions [⟨ou, hF.hH.SH.stateBytes⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩]) := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), h.h3, h.h4, h.h6, h.h7, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_is, h.d_uo, h.d_us, h.d_os, h.sp, h.b_i, h.b_u, h.b_o, h.b_s⟩

theorem fin_ok : ∀ s, (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).pre s → ∃ t s', Exec isa F.H.finalize s t s' ∧
    abiPreserved s s' ∧ (finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.PPC64LE.Finalize.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `r5`, into `o`, with the working space at `sc`. -/
theorem hf_call {s : State} {inn ou o sc : Addr} (h : HfArgs F s inn ou o sc) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨o, F.H.D⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] ++ [below s.sp 96]) s' →
      (∀ k0 text, k0.length = F.H.B → k0.length + text.length < 2 ^ 64 →
        hF.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .r5 = BitVec.ofNat 64 (F.H.B + text.length) →
        hF.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o F.H.D = hmacBlockKey hF.hH.SH.H k0 text) → Q s') :
    WP isa F.callHf s Q := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  obtain hfd : F.H.finalize.fdepth ≤ 2 := by
    have := VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth hF.hH
    simp only [Hash.finalize, Code.fdepth, Nat.max_le]; omega_arith
  obtain hpf : pushFrames F.H.finalize = true := by
    simp [Hash.finalize, pushFrames, Instr.isPush, VG.Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf hF.hH]
  obtain c3 : s.callEntry.gpr .r3 = inn := (State.callEntry_gpr _ (by decide)).trans h.h3
  obtain c4 : s.callEntry.gpr .r4 = ou := (State.callEntry_gpr _ (by decide)).trans h.h4
  obtain c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  obtain c6 : s.callEntry.gpr .r6 = o := (State.callEntry_gpr _ (by decide)).trans h.h6
  refine WP.callF (k := finG hF.hH.SH (F.H.W + 48 + F.H.FD) 96) (fin_ok hF) (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hS, hD]; exact h.hw) ?_ (by omega_arith) hpf
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf (by omega_arith) (by omega_arith)

include hF in
/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {P : State → State → Prop} {inn ou o sc : Addr}
    (h : ∀ s s', P s s' → HfArgs F s inn ou o sc ∧ HfArgs F s' inn ou o sc ∧ s.sp = s'.sp ∧
      s.gpr .r5 = s'.gpr .r5) :
    RelCT isa P F.callHf fun _ _ => True := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (fin_ok hF) hF.hfCt [⟨ou, hF.hH.SH.stateBytes⟩]
    [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩, ⟨sc, F.H.W + 48 + F.H.FD⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e5⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r4 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r5 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r7 ∉ linkRegs),
    a.h3, a'.h3, a.h4, a'.h4, a.h6, a'.h6, a.h7, a'.h7, e5]
  rw [e]; simp

/-! ## `iterate` -/

/-- What a call of `iterate` needs: the key's states at `key`, `U` at `u`,
`T` at `t` and the working space at `sc`. -/
structure ItArgs (F : Fns) (s : State) (key u t sc : Addr) : Prop where
  h3 : s.gpr .r3 = key
  h4 : s.gpr .r4 = u
  h6 : s.gpr .r6 = t
  h7 : s.gpr .r7 = sc
  sp : 96 ≤ s.sp.toNat
  d_kt : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨t, F.H.D⟩
  d_ks : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨sc, F.itW⟩
  d_ut : Region.Disjoint ⟨u, F.H.D⟩ ⟨t, F.H.D⟩
  d_us : Region.Disjoint ⟨u, F.H.D⟩ ⟨sc, F.itW⟩
  d_ts : Region.Disjoint ⟨t, F.H.D⟩ ⟨sc, F.itW⟩
  b_k : (below s.sp 96).Disjoint ⟨key, 2 * F.H.S⟩
  b_u : (below s.sp 96).Disjoint ⟨u, F.H.D⟩
  b_t : (below s.sp 96).Disjoint ⟨t, F.H.D⟩
  b_s : (below s.sp 96).Disjoint ⟨sc, F.itW⟩
  hc : Covers ([⟨key, 2 * F.H.S⟩, ⟨u, F.H.D⟩] ++ [⟨t, F.H.D⟩, ⟨sc, F.itW⟩])
    (s.rd ++ s.wr)
  hw : Covers [⟨t, F.H.D⟩, ⟨sc, F.itW⟩] s.wr

theorem ItArgs.pre {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) :
    (iterG hF.hH.SH F.itW 96).pre (s.callEntry.withRegions
      [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
      [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩]) := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [iterG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), h.h3, h.h4, h.h6, h.h7, hS, hD]
  exact ⟨trivial, trivial, h.d_kt, h.d_ks, h.d_ut, h.d_us, h.d_ts, h.sp, h.b_k, h.b_u, h.b_t, h.b_s⟩

theorem it_ok : ∀ s, (iterG hF.hH.SH F.itW 96).pre s → ∃ t s',
    Exec isa F.itC s t s' ∧ abiPreserved s s' ∧ (iterG hF.hH.SH F.itW 96).post s s' := hF.itOk

/-- `iterate` with the key's states at `key`, `U` at `u`, `n` in `r5`, `T` at
`t` and the working space at `sc`. -/
theorem it_call {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨t, F.H.D⟩, ⟨sc, F.itW⟩] ++ [below s.sp 96]) s' →
      (∀ k0, k0.length = F.H.B → hF.hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hF.hH.SH.Repr s.mem (key + BitVec.ofNat 64 F.H.S) (xorPad k0 opad) →
        bytesAt s'.mem t F.H.D = Spec.Pbkdf2.iterate (hmacBlockKey hF.hH.SH.H k0)
          ((s.gpr .r5).setWidth 32).toNat (bytesAt s.mem u F.H.D) (bytesAt s.mem t F.H.D)) → Q s') :
    WP isa F.callIt s Q := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have hfd := hF.itFd
  have hpf := hF.itPf
  obtain c3 : s.callEntry.gpr .r3 = key := (State.callEntry_gpr _ (by decide)).trans h.h3
  obtain c4 : s.callEntry.gpr .r4 = u := (State.callEntry_gpr _ (by decide)).trans h.h4
  obtain c5 : s.callEntry.gpr .r5 = s.gpr .r5 := State.callEntry_gpr _ (by decide)
  obtain c6 : s.callEntry.gpr .r6 = t := (State.callEntry_gpr _ (by decide)).trans h.h6
  refine WP.callF (k := iterG hF.hH.SH F.itW 96) (it_ok hF) (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hD]; exact h.hw) ?_ (by omega_arith) hpf
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [iterG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6,
    hD, hB, hS] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hD] at hf
  exact Frame.below_mono hf (by omega_arith) (by omega_arith)

include hF in
/-- Two runs of a call of `iterate` with the same arguments. -/
theorem it_rel {P : State → State → Prop} {key u t sc : Addr}
    (h : ∀ s s', P s s' → ItArgs F s key u t sc ∧ ItArgs F s' key u t sc ∧ s.sp = s'.sp ∧
      (s.gpr .r5).setWidth 32 = (s'.gpr .r5).setWidth 32) :
    RelCT isa P F.callIt fun _ _ => True := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (it_ok hF) hF.itCt [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
    [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e5⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hD]; exact a'.hw⟩
  simp only [iterG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r4 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r5 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r6 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r7 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.r7 ∉ linkRegs),
    a.h3, a'.h3, a.h4, a'.h4, a.h6, a'.h6, a.h7, a'.h7, e5]
  rw [e]; simp

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st`, the
`len` bytes at `dat` and the working space at `sc`. -/
structure UpdArgs (F : Fns) (s : State) (st dat sc : Addr) (len : Nat) : Prop where
  h3 : s.gpr .r3 = st
  h5 : s.gpr .r5 = dat
  h6 : (s.gpr .r6).toNat = len
  h7 : s.gpr .r7 = sc
  d₁ : Region.Disjoint ⟨st, F.H.S⟩ ⟨sc, F.H.W⟩
  d₂ : Region.Disjoint ⟨dat, len⟩ ⟨st, F.H.S⟩
  d₃ : Region.Disjoint ⟨dat, len⟩ ⟨sc, F.H.W⟩
  sp : 48 ≤ s.sp.toNat
  s₁ : (below s.sp 48).Disjoint ⟨st, F.H.S⟩
  s₂ : (below s.sp 48).Disjoint ⟨dat, len⟩
  s₃ : (below s.sp 48).Disjoint ⟨sc, F.H.W⟩
  hc : Covers ([⟨dat, len⟩] ++ [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩]) (s.rd ++ s.wr)
  hw : Covers [⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] s.wr

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call (hH : HashOK F.H) {s : State} {st dat sc : Addr} {len : Nat} (h : UpdArgs F s st dat sc len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, F.H.S⟩, ⟨sc, F.H.W⟩] ++ [below s.sp 48]) s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa F.H.callUpd s Q :=
  hH.callUpd_ok h.h3 h.h5 h.h6 h.h7 h.d₁ h.d₂ h.d₃ h.sp h.s₁ h.s₂ h.s₃ h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Pbkdf2.Whole.PPC64LE

end

end


/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: the setup

From the start of the frame (`framed`, the link register in `r0` pushed),
the prologue saves our caller's `r20`–`r25` and moves the arguments into
them (`prologue_ok`); HMAC's `init` makes the key's inner and outer states
(`States`, of `K₀`, the password made a key, `K0`); and `INT (1)` is stored
(`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved saveMem saveMem_saved saveMem_frame save_ok untouched)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_addi wp_li wp_stwbrx)
open Spec.Hmac (xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- The frame's push writes only the 48 bytes below the stack pointer. -/
theorem framed_frame {s : State} (r : Reg) : Frame [below s.sp 48] s.mem (framed r s).mem := by
  obtain c : ∀ off, off + 8 ≤ 48 → (below s.sp 48).Contains (s.sp - 48 + BitVec.ofNat 64 off) 8 := fun off ho => by
    simp only [Region.Contains]
    rw [show s.sp - 48 + BitVec.ofNat 64 off - (s.sp - BitVec.ofNat 64 48) = BitVec.ofNat 64 off by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (by simpa using c 0 (by omega_arith)))
    (List.mem_singleton_self _) _ (c 32 (by omega_arith))

/-- The state the frame's body starts in. -/
abbrev entry (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem entry_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (entry s₀).gpr r = s₀.gpr r := by
  simp [framed, State.write, h]

/-- After the prologue: `KR`, the output in `r23` and `r24`, and HMAC's
`init`'s arguments. -/
structure Pro (F : Fns) (X : Nat) (s₀ s : State) : Prop where
  kr : KR F X s₀ s
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r9
  r3 : s.gpr .r3 = sA s₀ F.st0O
  r4 : s.gpr .r4 = sA s₀ F.st1O
  r5 : s.gpr .r5 = pw s₀
  r6 : s.gpr .r6 = s₀.gpr .r4

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F hF.X s₀)
include hF hp

theorem prologue_ok : WP isa (.block F.prologue) (entry s₀) (Pro F hF.X s₀) := by
  obtain hz := sizes hF
  obtain hl := layout (F := F)
  have hb := hz.reach
  obtain hsp : 48 ≤ s₀.sp.toNat := by have := hp.sp; omega_arith
  unfold Fns.prologue
  refine save_ok (so := 0) ⟨rfl, by decide⟩ (b := .r10) (by decide)
    (fun d _ hd => by rw [entry_gpr s₀ (by decide)]; exact in_sc hp hz.reach rfl (by omega_arith))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_mov fun s₉ u₉ =>
    wp_addi (by omega_arith) fun s₁₀ u₁₀ => wp_addi (by omega_arith) fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain e : ∀ r, r ≠ .r0 → s₁.gpr r = s₀.gpr r := fun r h => by rw [g₁]; exact entry_gpr s₀ h
  obtain mm : s₁₁.mem = s₁.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain gg : ∀ r, r ∉ [Reg.r21, .r20, .r22, .r23, .r24, .r25, .r5, .r6, .r3, .r4] → s₁₁.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g, h, i, j, k⟩ := hr
    rw [u₁₁.other r k, u₁₀.other r j, u₉.other r i, u₈.other r h, u₇.other r g, u₆.other r f, u₅.other r d,
      u₄.other r c, u₃.other r b, u₂.other r a]
  obtain sv : Saved 0 (scr s₀) s₀.gpr s₁₁.mem := by
    rw [mm, m₁, show (entry s₀).gpr .r10 = scr s₀ from entry_gpr s₀ (by decide)]
    intro p hp'
    obtain h0 : p.1 ≠ .r0 := by
      simp only [Hash.savedAt, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [saveMem_saved (so := 0) ⟨rfl, by decide⟩ (entry s₀).mem (scr s₀) (entry s₀).gpr p hp', entry_gpr s₀ h0]
  obtain q20 : s₁₁.gpr .r20 = s₀.gpr .r6 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q21 : s₁₁.gpr .r21 = scr s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q22 : s₁₁.gpr .r22 = s₀.gpr .r7 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q23 : s₁₁.gpr .r23 = out s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q24 : s₁₁.gpr .r24 = s₀.gpr .r9 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q25 : s₁₁.gpr .r25 = salt s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q3 : s₁₁.gpr .r3 = sA s₀ F.st0O := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [e _ (by decide)]
  obtain q4 : s₁₁.gpr .r4 = sA s₀ F.st1O := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [e _ (by decide)]
  obtain q5 : s₁₁.gpr .r5 = pw s₀ := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  obtain q6 : s₁₁.gpr .r6 = s₀.gpr .r4 := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
      u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e _ (by decide)
  refine ⟨⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; rfl,
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; rfl,
    by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl,
    q20, q21, q22, q25, fun r hr => ?_, sv, ?_⟩, q23, q24, q3, q4, q5, q6⟩
  · rw [gg r (by revert r hr; decide), e r (by revert r hr; decide)]
  · rw [mm, m₁]
    obtain f1 : Frame [below s₀.sp 48] s₀.mem (entry s₀).mem := framed_frame (s := s₀.write .r0 s₀.lr) .r0
    refine (f1.sub fun r hr => ?_).trans ((saveMem_frame (so := 0) ⟨rfl, by decide⟩ _ _ _).sub
      fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stk hF.X s₀, by simp, below_sub (by omega_arith) (by have := hp.sp; have := s₀.sp.isLt; omega_arith)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨scR F s₀, by simp, ?_⟩
      rw [entry_gpr s₀ (by decide)]
      exact Region.sub_prefix (by omega_arith)

end

/-! ## HMAC's states for the key -/

/-- The key `K₀`: the password, or its digest, padded to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte := blockKey hF.hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- The key's inner and outer states. -/
def States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop :=
  hF.hH.SH.Repr m (sA s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧ hF.hH.SH.Repr m (sA s₀ F.st1O) (xorPad (K0 hF s₀) opad)

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

theorem sp_toNat : (s₀.sp - 48).toNat = s₀.sp.toNat - 48 := by
  have := hp.sp
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simp; omega_arith))]; rfl

theorem sA_toNat {o : Nat} (h : o < F.bytes) : (sA s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

omit hp in
/-- The key's states survive writes apart from them. -/
theorem States.keep {m m' : Mem} (h : States hF s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (2 * F.H.S)) r) : States hF s₀ m' := by
  obtain hz := sizes hF
  obtain hS : F.H.S ≤ 256 := by have := hz.N; have := hz.B; rw [hz.S]; omega_arith
  refine ⟨hF.hH.congr m m' _ _ (fun i hi => ?_) h.1, hF.hH.congr m m' _ _ (fun i hi => ?_) h.2⟩
  · exact hf.bytes (R := sR s₀ F.st0O F.H.S) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_arith)))
      (by show F.H.S ≤ 2 ^ 64; omega_arith) hi
  · have := hf.bytes (R := sR s₀ F.st0O (2 * F.H.S)) (hd · ·) (by show 2 * F.H.S ≤ 2 ^ 64; omega_arith)
      (i := F.H.S + i) (by show F.H.S + i < 2 * F.H.S; omega_arith)
    rwa [VG.Proof.Hmac.Stream.PPC64LE.add_off, show sA s₀ F.st0O + BitVec.ofNat 64 F.H.S = sA s₀ F.st1O by
      rw [← VG.Proof.Hmac.Stream.PPC64LE.add_off]; rfl] at this

end

/-- After HMAC's `init`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F hF.X s₀ s
  r23 : s.gpr .r23 = out s₀
  r24 : s.gpr .r24 = s₀.gpr .r9
  st : States hF s₀ s.mem

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F hF.X s₀)
include hF hp

/-- HMAC's `init`'s arguments, after the prologue. -/
theorem hi_args {s : State} (h : Pro F hF.X s₀ s) :
    HiArgs hF s (sA s₀ F.st0O) (sA s₀ F.st1O) (pw s₀) (pwl s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hsp := sp_toNat hp
  have hX := hF.hX
  obtain bsub : Region.Sub (below s.sp (hF.X + 96)) (stk hF.X s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega_arith)
  obtain p0 : Region.Sub (sR s₀ F.st0O F.H.S) (scR F s₀) := part_sub (by omega_arith)
  obtain p1 : Region.Sub (sR s₀ F.st1O F.H.S) (scR F s₀) := part_sub (by omega_arith)
  refine ⟨h.r3, h.r4, h.r5, by rw [h.r6], by rw [h.kr.sp, hsp]; have := hp.sp; omega_arith,
    part_disj hb (.inl (by omega_arith)) (by omega_arith) (by omega_arith), (hp.pw_s.sub_right p0).symm,
    (hp.pw_s.sub_right p1).symm, hp.b_s.sub_left bsub |>.sub_right p0, hp.b_s.sub_left bsub |>.sub_right p1,
    hp.b_pw.sub_left bsub, by rw [sA_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith,
    by rw [sA_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith, hp.npw, ?_, ?_⟩
  · rw [h.kr.rd, h.kr.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨pwR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR F s₀, by simp, F.st0O, rfl, by show F.st0O + F.H.S ≤ F.bytes; omega_arith⟩
    · exact ⟨scR F s₀, by simp, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.bytes; omega_arith⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.st0O, rfl, by show F.st0O + F.H.S ≤ F.bytes; omega_arith⟩
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.bytes; omega_arith⟩

theorem hi_ok {s : State} (h : Pro F hF.X s₀ s) : WP isa F.callHi s (Keyed hF s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hX := hF.hX
  refine hi_call hF (hi_args hF hp h) fun s' a hI hO => ?_
  obtain kr' := h.kr.call hp hb a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, _, rfl, by omega_arith, by omega_arith⟩
    · exact .inr ⟨_, by rw [h.kr.sp], by omega_arith⟩
  rw [h.kr.pwBytes hp] at hI hO
  exact ⟨kr', by rw [a.cs _ (by decide), h.r23], by rw [a.cs _ (by decide), h.r24], hI, hO⟩

end

end VG.Proof.Pbkdf2.Whole.PPC64LE

end

end


/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: a block, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `r23` points past them and `r24` counts the bytes left,
and `scratch` holds `INT (k + 1)`, byte-reversed. A block copies the key's
inner state into the working state (`HashOK.reloc`: it represents a whole
block), absorbs the salt and `INT (k + 1)` into it (`update`), and computes
`U₁` with HMAC's `finalize` (`u1_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_addi wp_li)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem blockKey_length (hH : HashOK F.H) (k : List Byte) : (blockKey hH.SH.H k).length = F.H.B := by
  obtain hB := hH.hB; have := hH.hDB
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hH.hashLen]; omega_arith
  · omega_arith

/-! ## After `k` blocks -/

section
variable (hF : FnsOK F) (s₀ : State)

/-- The salt. -/
abbrev saltB : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)
/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (K0 hF s₀)
/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (k : Nat) : List Byte := Whole.G (prf hF s₀) (saltB s₀) (cc s₀) k
abbrev Tk (i : Nat) : List Byte := Whole.Tb (prf hF s₀) (saltB s₀) (cc s₀) i
abbrev nbk : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

end

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR F hF.X s₀ s
  st : States hF s₀ s.mem
  r23 : s.gpr .r23 = out s₀ + BitVec.ofNat 64 (dn s₀ (F := F) k)
  r24 : s.gpr .r24 = BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k)
  intW : s.mem.readW (sA s₀ F.intO) 32 = rev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (out s₀) (dn s₀ (F := F) k) = (Gk hF s₀ k).take (dn s₀ (F := F) k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := .r23 :: .r24 :: kregs

/-- Where a block writes, before it copies `T` out: the working space of the
functions we call, the parts of `scratch` from the working state up to
`INT (i)`, and the stack below the frame. -/
def Wb (F : Fns) (X : Nat) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 48 ≤ o ∧ o + n ≤ F.st0O) ∨ (∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO) ∨
    ∃ n, r = below (s₀.sp - 48) n ∧ n + 48 ≤ X + 144

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

theorem Wb.ok {r : Region} (h : Wb F hF.X s₀ r) :
    Wk F hF.X s₀ r ∧ (sR s₀ F.st0O (2 * F.H.S)).Disjoint r ∧ (sR s₀ F.intO 4).Disjoint r ∧
      (outR s₀).Disjoint r := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | ⟨o, n, rfl, h₁, h₂⟩ | ⟨n, rfl, hn⟩
  · exact ⟨.inl ⟨o, n, rfl, h₁, by omega_arith⟩, part_disj hb (.inr h₂) (by omega_arith) (by omega_arith),
      part_disj hb (.inr (by omega_arith)) (by omega_arith) (by omega_arith), hp.o_s.sub_right (part_sub (by omega_arith))⟩
  · exact ⟨.inl ⟨o, n, rfl, by omega_arith, by omega_arith⟩, part_disj hb (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      part_disj hb (.inr h₂) (by omega_arith) (by omega_arith), hp.o_s.sub_right (part_sub (by omega_arith))⟩
  · have hsub := below_stk hp hn
    exact ⟨.inr ⟨n, rfl, hn⟩, (hp.b_s.sub_left hsub |>.sub_right (part_sub (by omega_arith))).symm,
      (hp.b_s.sub_left hsub |>.sub_right (part_sub (by omega_arith))).symm, (hp.b_o.sub_left hsub).symm⟩

/-- `Inv` survives writes where a block writes. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wb F hF.X s₀ r) : Inv hF s₀ k s' := by
  obtain hz := sizes hF; have hb := hz.reach
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) hf
      (fun r hr => (Wk.ok hp hb (Wb.ok hp (hw r hr)).1).1) (fun r hr => (Wk.ok hp hb (Wb.ok hp (hw r hr)).1).2),
    h.st.keep hf (fun r hr => (Wb.ok hp (hw r hr)).2.1), by rw [hg _ (by simp), h.r23],
    by rw [hg _ (by simp), h.r24], ?_, h.glen, ?_⟩
  · rw [← h.intW]
    exact hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => (Wb.ok hp (hw r hr)).2.2.1)
      (by decide)
  · rw [← h.outB]
    obtain osub : Region.Sub ⟨out s₀, dn s₀ (F := F) k⟩ (outR s₀) := Region.sub_prefix (Nat.min_le_right _ _)
    exact Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨out s₀, dn s₀ (F := F) k⟩)
      (fun r hr => ((Wb.ok hp (hw r hr)).2.2.2).sub_left osub)
      (by have e1 : dn s₀ (F := F) k ≤ ol s₀ := Nat.min_le_right _ _
          obtain e2 : ol s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
          show dn s₀ (F := F) k ≤ 2 ^ 64; omega_arith) hi

end

/-! ## A block, up to `U₁` -/

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- Copying `n` words from offset `a` of `scratch` to offset `b`, where a
block writes. -/
theorem copy_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {a b n : Nat} (hab : a + 4 * n ≤ b ∨ b + 4 * n ≤ a)
    (ha : a + 4 * n ≤ F.bytes) (hw : Wb F hF.X s₀ (sR s₀ b (4 * n))) (hbo : b + 4 * n ≤ F.bytes)
    {rest : List Instr} {Q : State → Prop}
    (hk : ∀ t, Inv hF s₀ k t → (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) →
      t.mem = writeBytes s.mem (sA s₀ b) (bytesAt s.mem (sA s₀ a) (4 * n)) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (Impl.Hmac.Stream.PPC64LE.Hash.cp32 .r21 .r21 a b) ++ rest)) s Q := by
  obtain hz := sizes hF; have hb := hz.reach
  obtain e : ∀ o j, s.gpr .r21 + BitVec.ofNat 64 o + BitVec.ofNat 64 j = sA s₀ (o + j) := fun o j => by
    rw [h.kr.r21, ← VG.Proof.Hmac.Stream.PPC64LE.add_off]
  refine VG.Proof.Hmac.Stream.PPC64LE.copy32_ok (src := .r21) (dst := .r21) (by decide) (by decide) (by decide)
    (by decide) a b n ⟨by omega_arith, by omega_arith⟩ rest s Q
    (fun j hj => by rw [e]; exact in_sc' hp hb h.kr.wr (by omega_arith))
    (fun j hj => by rw [e]; exact in_sc hp hb h.kr.wr (by omega_arith))
    (by rw [h.kr.r21]; exact Offset.sep _ hab (by have := hp.nsc; omega_arith) (by have := hp.nsc; omega_arith))
    fun t g rd wr sp m => ?_
  rw [h.kr.r21] at m
  refine hk t (h.keep hp rd wr sp (fun r hr => g r (by revert r; decide)) (rs := [sR s₀ b (4 * n)]) ?_
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hw)) g m
  rw [m]
  exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

/-- The key's inner state copied into the working state, which then
represents `K₀ ⊕ ipad`, and `update`'s arguments for the salt. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block (F.copyW ++ F.saltArgs)) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad) ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = BitVec.ofNat 64 F.H.B ∧ t.gpr .r5 = salt s₀ ∧ t.gpr .r6 = s₀.gpr .r6 ∧
      t.gpr .r7 = sA s₀ 48 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hS4 : 4 * (F.H.S / 4) = F.H.S := by have := hz.N4; have := hz.S; rcases hz.B with h | h <;> omega_arith
  unfold Fns.copyW Fns.saltArgs
  refine copy_ok hp h (a := F.st0O) (b := F.stWO) (n := F.H.S / 4) (by omega_arith) (by omega_arith)
    (.inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega_arith⟩)) (by omega_arith) fun t ht g m => ?_
  refine wp_addi (by omega_arith) fun s₁ u₁ => wp_li (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨ht.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm]
    obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    refine hF.hH.reloc s.mem t.mem _ _ _ (by rw [xorPad_length, hK]; exact Nat.mod_self _) (fun i hi => ?_) h.st.1
    have := hz.S
    rw [hS4] at m
    rw [m, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [bytesAt_length]; omega_arith)
      (by rw [bytesAt_length]; omega_arith), VG.Proof.Hmac.Common.bytesAt_getD' _ _ (by omega_arith)]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r25]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r20]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]; rfl

end

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- The salt and `scratch` fit in the address space together. -/
theorem sl_bytes : sl s₀ + F.bytes ≤ 2 ^ 64 :=
  Whole.len_add_le hp.sa_s hp.nsa hp.nsc

theorem below48 {s : State} (h : KR F hF.X s₀ s) {n : Nat} (hn : n + 48 ≤ hF.X + 144) :
    Region.Sub (below s.sp n) (stk hF.X s₀) := by
  rw [h.sp]; exact below_stk hp hn

/-- `update`'s arguments for the working state, with the `len` bytes at `dat`. -/
theorem updW_args {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat}
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h5 : s.gpr .r5 = dat) (h6 : (s.gpr .r6).toNat = len)
    (h7 : s.gpr .r7 = sA s₀ 48) (hd₂ : Region.Disjoint ⟨dat, len⟩ (sR s₀ F.stWO F.H.S))
    (hd₃ : Region.Disjoint ⟨dat, len⟩ (sR s₀ 48 F.H.W)) (hs₂ : (stk hF.X s₀).Disjoint ⟨dat, len⟩)
    (hcd : ∃ r' ∈ s.rd ++ s.wr, ∃ off, dat = r'.base + BitVec.ofNat 64 off ∧ off + len ≤ r'.len) :
    UpdArgs F s (sA s₀ F.stWO) dat (sA s₀ 48) len := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hWc := hz.Wc; have hD := hz.D; have hN := hz.N; have hSS := hz.S; have hB := hz.B
  obtain hsp := sp_toNat hp
  obtain bs := below48 hp h.kr (n := 48) (by omega_arith)
  refine ⟨h3, h5, h6, h7, part_disj hb (.inr (by omega_arith)) (by omega_arith) (by omega_arith), hd₂, hd₃,
    by rw [h.kr.sp, hsp]; have := hp.sp; omega_arith, hp.b_s.sub_left bs |>.sub_right (part_sub (by omega_arith)),
    hs₂.sub_left bs, hp.b_s.sub_left bs |>.sub_right (part_sub (by omega_arith)), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hcd
    · exact ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), F.stWO, rfl,
        by show F.stWO + F.H.S ≤ F.bytes; omega_arith⟩
    · exact ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), 48, rfl, by show 48 + F.H.W ≤ F.bytes; omega_arith⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.stWO, rfl, by show F.stWO + F.H.S ≤ F.bytes; omega_arith⟩
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, 48, rfl, by show 48 + F.H.W ≤ F.bytes; omega_arith⟩

/-- `update` of the working state, from `m`, with the `len` bytes at `dat`. -/
theorem updW_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat} {m : List Byte}
    (ha : UpdArgs F s (sA s₀ F.stWO) dat (sA s₀ 48) len)
    (hm : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) (h4 : s.gpr .r4 = BitVec.ofNat 64 m.length) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (m ++ bytesAt s.mem dat len) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hWc := hz.Wc; have hD := hz.D; have hSS := hz.S
  refine upd_call hF.hH ha fun t a hu => ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide))
    a.frame fun r hr => ?_, hu m hm h4⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega_arith⟩)
  · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega_arith⟩
  · exact .inr (.inr ⟨48, by rw [h.kr.sp], by omega_arith⟩)

end

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- `update`'s arguments for the salt. -/
theorem b2_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h5 : s.gpr .r5 = salt s₀) (h6 : s.gpr .r6 = s₀.gpr .r6) (h7 : s.gpr .r7 = sA s₀ 48) :
    UpdArgs F s (sA s₀ F.stWO) (salt s₀) (sA s₀ 48) (sl s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hWc := hz.Wc; have hSS := hz.S
  exact updW_args hp h h3 h5 (by rw [h6]) h7
    (hp.sa_s.sub_right (part_sub (by omega_arith))) (hp.sa_s.sub_right (part_sub (by omega_arith))) hp.b_sa
    ⟨saltR s₀, List.mem_append_left _ (by rw [h.kr.rd, hp.rd]; simp), 0, by simp, by simp⟩

/-- The salt absorbed into the working state. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad)) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 F.H.B) (h5 : s.gpr .r5 = salt s₀) (h6 : s.gpr .r6 = s₀.gpr .r6)
    (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hWc := hz.Wc; have hSS := hz.S
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine WP.mono (updW_ok hp h (b2_args hp h h3 h5 h6 h7) hr
    (by rw [h4, xorPad_length, hK])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [h.kr.saltBytes hp] at hu

/-- `update`'s arguments for `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = BitVec.ofNat 64 (F.H.B + sl s₀) ∧ t.gpr .r5 = sA s₀ F.intO ∧ t.gpr .r6 = BitVec.ofNat 64 4 ∧
      t.gpr .r7 = sA s₀ 48 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  unfold Fns.updArgs
  refine wp_addi (by omega_arith) fun s₁ u₁ => wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_addi (by omega_arith) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain mm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r20]
    obtain hsum : F.H.B + sl s₀ < 2 ^ 64 := by
      have := sl_bytes hp; have := hz.S; have := hz.Wc; omega_arith
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .r6).toNat + F.H.B % 2 ^ 64) % 2 ^ 64 = (F.H.B + (s₀.gpr .r6).toNat) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B) (by omega_arith), Nat.add_comm]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]; rfl

/-- `update`'s arguments for `INT (k + 1)`. -/
theorem b4_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h5 : s.gpr .r5 = sA s₀ F.intO) (h6 : s.gpr .r6 = BitVec.ofNat 64 4) (h7 : s.gpr .r7 = sA s₀ 48) :
    UpdArgs F s (sA s₀ F.stWO) (sA s₀ F.intO) (sA s₀ 48) 4 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  obtain hsub : Region.Sub ⟨sA s₀ F.intO, 4⟩ (scR F s₀) := part_sub (by omega_arith)
  exact updW_args hp h h3 h5 (by rw [h6]; rfl) h7
    (part_disj hb (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (part_disj hb (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
    (hp.b_s.sub_right hsub) ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), F.intO, rfl,
      by show F.intO + 4 ≤ F.bytes; omega_arith⟩

/-- `INT (k + 1)` absorbed into the working state. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀))
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = BitVec.ofNat 64 (F.H.B + sl s₀))
    (h5 : s.gpr .r5 = sA s₀ F.intO) (h6 : s.gpr .r6 = BitVec.ofNat 64 4) (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  obtain hsub : Region.Sub ⟨sA s₀ F.intO, 4⟩ (scR F s₀) := part_sub (by omega_arith)
  refine WP.mono (updW_ok hp h (b4_args hp h h3 h5 h6 h7) hr
    (by rw [h4, List.length_append, xorPad_length, hK, bytesAt_length])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [Whole.bytes_rev_int (i := k + 1) (by rw [h.intW]; rfl)] at hu

end

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- HMAC's `finalize`'s arguments. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = sA s₀ F.st1O ∧ t.gpr .r5 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧ t.gpr .r6 = sA s₀ F.uO ∧
      t.gpr .r7 = sA s₀ 48 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  unfold Fns.finArgs
  refine wp_addi (by omega_arith) fun s₁ u₁ => wp_addi (by omega_arith) fun s₂ u₂ =>
    wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₃ u₃ => wp_addi (by omega_arith) fun s₄ u₄ =>
    wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain mm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r20]
    obtain hsum : F.H.B + (sl s₀ + 4) < 2 ^ 64 := by
      have := sl_bytes hp; have := hz.S; have := hz.Wc; omega_arith
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .r6).toNat + (F.H.B + 4) % 2 ^ 64) % 2 ^ 64 = (F.H.B + ((s₀.gpr .r6).toNat + 4)) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B + 4) (by omega_arith)]
    congr 1; omega_arith
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]; rfl

/-- HMAC's `finalize`'s arguments. -/
theorem b6_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = sA s₀ F.st1O) (h6 : s.gpr .r6 = sA s₀ F.uO)
    (h7 : s.gpr .r7 = sA s₀ 48) : HfArgs F s (sA s₀ F.stWO) (sA s₀ F.st1O) (sA s₀ F.uO) (sA s₀ 48) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  obtain hWc := hz.Wc; have hSS := hz.S; have hD := hz.D; have hN := hz.N; have hB := hz.B
  obtain hsp := sp_toNat hp
  obtain bs := below48 hp h.kr (n := 96) (by omega_arith)
  obtain pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ F.bytes → b + n ≤ F.bytes →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj hb h₁ h₂ h₃
  obtain bp : ∀ {o n : Nat}, o + n ≤ F.bytes → (below s.sp 96).Disjoint (sR s₀ o n) := fun h' =>
    hp.b_s.sub_left bs |>.sub_right (part_sub h')
  obtain cv : ∀ {o n : Nat}, o + n ≤ F.bytes → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun {o n} h' => ⟨scR F s₀, sc_wr hp h.kr.wr, o, rfl, h'⟩
  refine ⟨h3, h4, h6, h7, by rw [h.kr.sp, hsp]; have := hp.sp; omega_arith,
    pd (.inr (by omega_arith)) (by omega_arith) (by omega_arith), pd (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
    pd (.inr (by omega_arith)) (by omega_arith) (by omega_arith), pd (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
    pd (.inr (by omega_arith)) (by omega_arith) (by omega_arith), pd (.inr (by omega_arith)) (by omega_arith) (by omega_arith),
    bp (by omega_arith), bp (by omega_arith), bp (by omega_arith), bp (by omega_arith), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain cv' : ∀ o n, o + n ≤ F.bytes → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
        (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
      obtain ⟨r', hr', off, e, l⟩ := cv h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' F.st1O F.H.S (by omega_arith)
    · exact cv' F.stWO F.H.S (by omega_arith)
    · exact cv' F.uO F.H.D (by omega_arith)
    · exact cv' 48 (F.H.W + 48 + F.H.FD) (by omega_arith)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cv (o := F.stWO) (n := F.H.S) (by omega_arith)
    · exact cv (o := F.uO) (n := F.H.D) (by omega_arith)
    · exact cv (o := 48) (n := F.H.W + 48 + F.H.FD) (by omega_arith)

/-- `U₁`, with HMAC's `finalize`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = sA s₀ F.st1O)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4))) (h6 : s.gpr .r6 = sA s₀ F.uO)
    (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.callHf s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine hf_call hF (b6_args hp h h3 h4 h6 h7) fun t a hf => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega_arith⟩)
    · exact .inr (.inl ⟨_, _, rfl, by omega_arith, by omega_arith⟩)
    · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega_arith⟩
    · exact .inr (.inr ⟨96, by rw [h.kr.sp], by omega_arith⟩)
  · have hl' : (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)).length = sl s₀ + 4 := by
      simp [bytesAt_length, Spec.Pbkdf2.int]
    refine hf (K0 hF s₀) _ (by rw [hK]) (by rw [hK, hl']; have := sl_bytes hp; omega_arith)
      (by rw [← List.append_assoc]; exact hr) (by rw [h5, hl']) h.st.2

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
