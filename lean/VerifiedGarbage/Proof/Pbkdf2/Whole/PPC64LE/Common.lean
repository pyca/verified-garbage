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
  itCt : ConstantTime isa (iterG hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96).pre
    (iterG hH.SH (Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H) 96).pub (Impl.Pbkdf2.Stream.PPC64LE.iterate F.H)
  /-- The working space of every function we call fits in `Wc` bytes. -/
  hWc : Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes F.H ≤ F.Wc
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
/-- The save area. -/
abbrev svR : Region := sR s₀ 0 48
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
  omega

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
  have hN := hF.hH.dims.N; have hB := hF.hH.dims.B; have hW := hF.hH.dims.so
  have hb := hF.hWc
  simp only [Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes, Impl.Pbkdf2.Stream.PPC64LE.Iter.ub,
    Impl.Pbkdf2.Stream.PPC64LE.Iter.dig, Impl.Pbkdf2.Stream.PPC64LE.Iter.st] at hb
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
  Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem part_contains (hr : F.bytes ≤ 4096) {o n : Nat} (h : o + n ≤ F.bytes) :
    (scR F s₀).Contains (sA s₀ o) n :=
  Offset.contains_base _ h (by omega)

theorem sc_wr {s : State} (hwr : s.wr = s₀.wr) : scR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem out_wr {s : State} (hwr : s.wr = s₀.wr) : outR s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem in_sc (hr : F.bytes ≤ 4096) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.bytes) :
    InRegions s.wr (sA s₀ o) n :=
  ⟨_, sc_wr hp hwr, part_contains (s₀ := s₀) hr h⟩

theorem in_sc' (hr : F.bytes ≤ 4096) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.bytes) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (sc_wr hp hwr), part_contains (s₀ := s₀) hr h⟩

/-- A part of `scratch` is covered by its regions. -/
theorem cov_part {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.bytes) :
    Covers [sR s₀ o n] s.wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, sc_wr hp hwr, o, rfl, h⟩

/-- The stack below the stack pointer of the frame. -/
theorem below_stk {n : Nat} (hn : n + 48 ≤ X + 144) : Region.Sub (below (s₀.sp - 48) n) (stk X s₀) :=
  fun x hx => below_sub hn (by have := hp.sp; have := s₀.sp.isLt; omega) x (below_body s₀.sp n x hx)

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

theorem KR.same {s s' : State} (h : KR F X s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F X s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

open VG.Proof.MdStream.PPC64LE (Upd Mupd) in
theorem KR.upd {s s' : State} (h : KR F X s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR F X s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A part of `scratch` after the save area, or the stack below the frame. -/
def Wk (F : Fns) (X : Nat) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 48 ≤ o ∧ o + n ≤ F.bytes) ∨ ∃ n, r = below (s₀.sp - 48) n ∧ n + 48 ≤ X + 144

theorem Wk.ok (hp : Pre F X s₀) (hr : F.bytes ≤ 4096) {r : Region} (h : Wk F X s₀ r) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 0, 48⟩ r ∧ ∃ r' ∈ wrs F X s₀, Region.Sub r r' := by
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) hr (.inl h₁) (by omega) h₂, _, by simp, part_sub (s₀ := s₀) h₂⟩
  · exact ⟨((hp.b_s.sub_left (below_stk hp hn)).sub_right (part_sub (s₀ := s₀) (o := 0) (n := 48) (by
      have := hr; simp only [Fns.bytes, Fns.intO, Fns.tO, Fns.uO, Fns.stWO, Fns.st1O, Fns.st0O,
        Fns.cO]; omega))).symm, _, by simp, below_stk hp hn⟩

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
    · exact hp.b_pw.symm) (by show (s₀.gpr .r4).toNat ≤ 2 ^ 64; have := (s₀.gpr .r4).isLt; omega)

theorem KR.saltBytes (hp : Pre F X s₀) {s : State} (hk : KR F X s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by show (s₀.gpr .r6).toNat ≤ 2 ^ 64; have := (s₀.gpr .r6).isLt; omega)

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
