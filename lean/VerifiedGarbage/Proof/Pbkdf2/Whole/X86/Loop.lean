module

import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Sha256.X86.Compress
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls
import VerifiedGarbage.Proof.Framework.OffsetBelow

/-! ### `Pbkdf2.Whole.X86.Block`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Whole.X86.Key`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Whole.X86.Common`, which this module and modules that import it used -/

section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the functions it calls, and its parts

`FnsOK F` is what the proof knows of the functions `pbkdf2` calls: the hash
function's streaming functions (`VG.Proof.Pbkdf2.Stream.X86.HashOK`), and
HMAC's `init` and `finalize` and PBKDF2's `iterate`, sound for their shared
contracts with 48 bytes of stack (`Sound`), with some working space each, at
most the `8 W` bytes they get. Then the precondition of `pbkdf2` (`Pre`), the
parts of its `scratch`, and what every piece of it keeps (`KR`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK SavedRegs saveR)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open Spec.Sha256 (bytesAt)

/-- The functions `pbkdf2` calls, verified. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  Wi : Nat
  Wf : Nat
  Wt : Nat
  hi : Sound F.hiC (Proof.Hmac.initScratchContract hH.SH Wi X86.abi 48)
  hf : Sound F.hfC (Proof.Hmac.finalizeScratchContract hH.SH Wf X86.abi 48)
  it : Sound F.itC (Proof.Pbkdf2.iterateContract hH.SH Wt X86.abi 48)
  hiSp : NoSp F.hiC
  hfSp : NoSp F.hfC
  itSp : NoSp F.itC
  hiSU : stackUse F.hiC ≤ 48
  hfSU : stackUse F.hfC ≤ 48
  itSU : stackUse F.itC ≤ 48
  hWi : Wi ≤ F.W
  hWf : Wf ≤ F.W
  hWt : Wt ≤ F.W
  hWH : F.H.W ≤ F.W
  hW : F.W ≤ 512
  /-- The digest is no longer than a block (so that the digest of a long
  password is a key `init` takes). -/
  hDB : F.H.D ≤ F.H.B
  /-- The streaming state holds a block. -/
  hBS : F.H.B ≤ F.H.S
  /-- Our buffers fit in the `8 S` bytes after the working space. -/
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev pw : BitVec 32 := arg s₀ 0
abbrev pwl : Nat := (arg s₀ 1).toNat
abbrev salt : BitVec 32 := arg s₀ 2
abbrev sl : Nat := (arg s₀ 3).toNat
/-- The iteration count. -/
abbrev cc : Nat := (arg s₀ 4).toNat
abbrev out : BitVec 32 := arg s₀ 5
abbrev ol : Nat := (arg s₀ 6).toNat
abbrev scr : BitVec 32 := arg s₀ 7
abbrev pwR : Region := ⟨(pw s₀).setWidth 64, pwl s₀⟩
abbrev saltR : Region := ⟨(salt s₀).setWidth 64, sl s₀⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, ol s₀⟩
abbrev scR (F : Fns) : Region := ⟨(scr s₀).setWidth 64, (F.W + F.H.S) * 8⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 32⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 76
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨(scr s₀).setWidth 64, k⟩

end

/-- The size of `scratch`. -/
abbrev _root_.VG.Impl.Pbkdf2.Whole.X86.Fns.L8 (F : Fns) : Nat := (F.W + F.H.S) * 8

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp76 : 76 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 36 ≤ 2 ^ 32
  rd : s₀.rd = [pwR s₀, saltR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR s₀ F]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  pw_s : (pwR s₀).Disjoint (scR s₀ F)
  pw_a : (pwR s₀).Disjoint (argR s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  sa_s : (saltR s₀).Disjoint (scR s₀ F)
  sa_a : (saltR s₀).Disjoint (argR s₀)
  o_s : (outR s₀).Disjoint (scR s₀ F)
  o_a : (outR s₀).Disjoint (argR s₀)
  s_a : (scR s₀ F).Disjoint (argR s₀)
  r_pw : (retR s₀).Disjoint (pwR s₀)
  r_sa : (retR s₀).Disjoint (saltR s₀)
  r_o : (retR s₀).Disjoint (outR s₀)
  r_s : (retR s₀).Disjoint (scR s₀ F)
  r_a : (retR s₀).Disjoint (argR s₀)
  b_pw : (stkR s₀).Disjoint (pwR s₀)
  b_sa : (stkR s₀).Disjoint (saltR s₀)
  b_o : (stkR s₀).Disjoint (outR s₀)
  b_s : (stkR s₀).Disjoint (scR s₀ F)
  b_a : (stkR s₀).Disjoint (argR s₀)
  npw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 32
  nsa : (salt s₀).toNat + sl s₀ ≤ 2 ^ 32
  no : (out s₀).toNat + ol s₀ ≤ 2 ^ 32
  nsc : (scr s₀).toNat + F.L8 ≤ 2 ^ 32
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

theorem pre_of (hF : FnsOK F) {s₀ : State} (h : (pbkN hF.hH.SH (F.W + F.H.S)).pre s₀) : Pre F s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hD := hF.hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩ : Region) = stkR s₀ := by
    rw [stkR, below_eq h0]
  rw [hD] at h28
  rw [e] at h18 h19 h20 h21 h22
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-! ## The layout of `scratch` -/

/-- The sizes, as facts about natural numbers. -/
structure Sizes (F : Fns) : Prop where
  B : 0 < F.H.B ∧ F.H.B ≤ 128
  S : 0 < F.H.S ∧ F.H.S ≤ 256
  D : 0 < F.H.D ∧ F.H.D ≤ F.H.F ∧ F.H.F ≤ 64
  W : F.H.W ≤ F.W ∧ F.W ≤ 512
  DB : F.H.D ≤ F.H.B
  BS : F.H.B ≤ F.H.S
  fits : 20 + 2 * F.H.D + F.H.F ≤ 4 * F.H.S

theorem FnsOK.sizes (hF : FnsOK F) : Sizes F :=
  ⟨⟨hF.hH.hB0, hF.hH.hBB⟩, ⟨hF.hH.hS0, hF.hH.hSB⟩, ⟨hF.hH.hD0, hF.hH.hDF, hF.hH.hF⟩, ⟨hF.hWH, hF.hW⟩, hF.hDB, hF.hBS, hF.fits⟩

/-- Where the parts of `scratch` are. -/
theorem layout : F.L.buf = 8 * F.W + 16 ∧ F.st0O = 8 * F.W + 16 ∧ F.st1O = 8 * F.W + 16 + F.H.S ∧
    F.stSO = 8 * F.W + 16 + 2 * F.H.S ∧ F.stWO = 8 * F.W + 16 + 3 * F.H.S ∧
    F.uO = 8 * F.W + 16 + 4 * F.H.S ∧ F.tO = 8 * F.W + 16 + 4 * F.H.S + F.H.D ∧
    F.hkO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D ∧ F.intO = 8 * F.W + 16 + 4 * F.H.S + 2 * F.H.D + F.H.F := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stSO, Fns.stWO, Fns.uO, Fns.tO, Fns.hkO, Fns.intO, Fns.L, Hash.buf]
  omega_using []

theorem end_le (hz : Sizes F) : F.intO + 4 ≤ F.L8 := by
  have := layout (F := F); have := hz.fits; simp only [Fns.L8]; omega_arith

/-! Bounds of the parts of `scratch`, each proved once for the many places that
need it (each an `omega` call of its own otherwise), down the chain of their
definitions from `end_le`, without `omega`. -/

theorem Sizes.intO_le (hz : Sizes F) : F.intO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ 4) (end_le hz)
theorem Sizes.hkO_F (hz : Sizes F) : F.hkO + F.H.F ≤ F.L8 := hz.intO_le
theorem Sizes.hkO_le (hz : Sizes F) : F.hkO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.hkO_F
theorem Sizes.hkO_D (hz : Sizes F) : F.hkO + F.H.D ≤ F.L8 :=
  Nat.le_trans (Nat.add_le_add_left hz.D.2.1 _) hz.hkO_F
theorem Sizes.tO_D (hz : Sizes F) : F.tO + F.H.D ≤ F.L8 := hz.hkO_le
theorem Sizes.tO_le (hz : Sizes F) : F.tO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.tO_D
theorem Sizes.uO_D (hz : Sizes F) : F.uO + F.H.D ≤ F.L8 := hz.tO_le
theorem Sizes.uO_le (hz : Sizes F) : F.uO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.uO_D
theorem Sizes.stWO_S (hz : Sizes F) : F.stWO + F.H.S ≤ F.L8 := hz.uO_le
theorem Sizes.stWO_le (hz : Sizes F) : F.stWO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.stWO_S
theorem Sizes.stSO_S (hz : Sizes F) : F.stSO + F.H.S ≤ F.L8 := hz.stWO_le
theorem Sizes.stSO_le (hz : Sizes F) : F.stSO ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.stSO_S
theorem Sizes.st1O_S (hz : Sizes F) : F.st1O + F.H.S ≤ F.L8 := hz.stSO_le
theorem Sizes.st1O_le (hz : Sizes F) : F.st1O ≤ F.L8 := Nat.le_trans (Nat.le_add_right _ _) hz.st1O_S
theorem Sizes.st0O_S (hz : Sizes F) : F.st0O + F.H.S ≤ F.L8 := hz.st1O_le
theorem Sizes.st0O_2S (hz : Sizes F) : F.st0O + 2 * F.H.S ≤ F.L8 := by
  rw [Nat.two_mul, ← Nat.add_assoc]; exact hz.stSO_le
theorem Sizes.st0O_3S (hz : Sizes F) : F.st0O + 3 * F.H.S ≤ F.L8 := by
  rw [show 3 * F.H.S = F.H.S + F.H.S + F.H.S from by rw [Nat.succ_mul, Nat.two_mul], ← Nat.add_assoc,
    ← Nat.add_assoc]
  exact hz.stWO_le
theorem Sizes.st0O_lt (hz : Sizes F) : F.st0O < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.S.1) hz.st0O_S
theorem Sizes.st1O_lt (hz : Sizes F) : F.st1O < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.S.1) hz.st1O_S
theorem Sizes.stWO_lt (hz : Sizes F) : F.stWO < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.S.1) hz.stWO_S
theorem Sizes.uO_lt (hz : Sizes F) : F.uO < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.D.1) hz.uO_D
theorem Sizes.tO_lt (hz : Sizes F) : F.tO < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.D.1) hz.tO_D
theorem Sizes.hkO_lt (hz : Sizes F) : F.hkO < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hz.D.1) hz.hkO_D
theorem Sizes.intO_lt (hz : Sizes F) : F.intO < F.L8 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) (end_le hz)
theorem Sizes.stWO_S_intO (_hz : Sizes F) : F.stWO + F.H.S ≤ F.intO :=
  show F.uO ≤ F.intO from Nat.le_trans (Nat.le_add_right F.uO F.H.D)
    (Nat.le_trans (Nat.le_add_right F.tO F.H.D) (Nat.le_add_right F.hkO F.H.F))

theorem L8_le (hz : Sizes F) : F.L8 ≤ 8 * 512 + 8 * 256 := by
  have := hz.W; have := hz.S; simp only [Fns.L8]; omega_arith

/-- The save area of our caller's registers. -/
abbrev svR (F : Fns) (s₀ : State) : Region := saveR F.L (scr s₀)

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : (dO s₀ o).setWidth 64 = A s₀ o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.setWidth_add (by omega_using [ho, this])

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc; exact Pbkdf2.Stream.X86.toNat_add_ofNat (by omega_using [ho, this])

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR s₀ F) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.disjoint _ h (by omega_using [ha, this]) (by omega_using [hb, this])

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := L8_le hz; exact Offset.base_disjoint _ hk (by omega_using [hbn, this])

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR s₀ F) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR s₀ F) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 16 ≤ F.L8; omega_arith)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := L8_le hz; exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega_using [ho])) (by simp only [Fns.L]; omega_using [ho, hon, this]) (by omega_using [hon, this])

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := L8_le hz; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 16) (by simp only [Fns.L]; omega_using [hk])
    (by simp only [Fns.L]; omega_arith)).symm

omit hz in
theorem sc_mem : scR s₀ F ∈ s₀.wr := by rw [hp.wr]; simp

theorem in_sc {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.L8) :
    InRegions s.wr (A s₀ o) n := by
  have := L8_le hz
  exact ⟨scR s₀ F, by rw [hwr]; exact sc_mem hp, Offset.contains_base _ h (by omega_using [h, this])⟩

end

/-! ## What every piece keeps -/

/-- The regions everything writes: `out`, `scratch` and the stack below `esp`. -/
abbrev wrs (F : Fns) (s₀ : State) : List Region := [outR s₀, scR s₀ F, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs F.L (scr s₀) s₀ s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

/-- The 76 bytes below `esp`, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : KR F s₀ s) : VG.Proof.Pbkdf2.Whole.X86.stk s = stkR s₀ := by
  rw [VG.Proof.Pbkdf2.Whole.X86.stk, h.esp]

/-- `KR` survives changes to other registers, and to memory in `out`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') :
    KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : VG.Proof.Sha256.X86.Stream.Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A write to a part of `scratch` after the save area. -/
theorem KR.write {s₀ s s' : State} (hz : Sizes F) (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : 8 * F.W + 16 ≤ o) (hon : o + n ≤ F.L8)
    (hf : Frame [sR s₀ o n] s.mem s'.mem) : KR F s₀ s' :=
  h.keep hrd hwr hg hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sv_disj hz ho hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, part_sub hon⟩)

/-- What a call leaves, writing parts of `scratch` after the save area, or
the working space, and the stack below `esp`. -/
theorem KR.call {s₀ s s' : State} (hp : Pre F s₀) (hz : Sizes F) (h : KR F s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = sR s₀ o n ∧ 8 * F.W + 16 ≤ o ∧ o + n ≤ F.L8) : KR F s₀ s' := by
  have hL := end_le hz; have := layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact sv_low hz hk
      · exact sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨scR s₀ F, by simp, low_sub (F := F) (by omega_using [hL, this, hk])⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The arguments, the return address and the inputs, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
theorem argR_eq : argR s₀ = ⟨addr (E s₀) 4, 32⟩ := rfl

theorem KR.argEq {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 8) : arg s i = arg s₀ i := by
  have hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨addr (E s₀) 4, 32⟩ r := by
    rw [← argR_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.o_a.symm
    · exact hp.s_a.symm
    · exact hp.b_a.symm
  exact Pbkdf2.Stream.X86.arg_keep rfl hk.esp (n := 32) (by have := hp.spf; omega) hk.frame hd (by omega_using [hi])

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [show s.ea (at_ .esp (4 + 4 * i)) = addr (s.gpr .esp) (4 + 4 * i) from rfl, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 8) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.wr]
  exact ⟨argR s₀, by simp, by
    rw [argR_eq]; exact Pbkdf2.Stream.X86.arg_contains rfl (by omega_using [hi]) (by have := hp.spf; omega)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR F s₀ s) {i : Nat} (hi : i < 8) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by
    rw [Pbkdf2.Stream.X86.argAddr_eq, Pbkdf2.Stream.X86.argAddr_eq, hk.esp]] at this

/-- `mov d, [esp + 4 + 4 i]`: argument `i`, while `KR` holds. -/
theorem wp_arg {s : State} (hk : KR F s₀ s) {d : Reg} {i : Nat} (hi : i < 8) {is : List Instr}
    {Q : State → Prop} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (Fns.argM i) :: is)) s Q :=
  VG.Proof.Sha256.X86.Stream.wp_movm (a := argAddr s₀ i) (argW hk.esp i) (argIn hp hk.rd hk.wr hi)
    fun s' u => k s' (by rw [hk.readArg hp hi] at u; exact u)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR F s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_o
    · exact hp.r_s
    · rw [stkR, below_eq hp.sp76]
      exact (Offset.below_disjoint _ (by omega_using [])).symm) (by decide)

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.pwBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((pw s₀).setWidth 64) (pwl s₀) = bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.pw_o
    · exact hp.pw_s
    · exact hp.b_pw.symm) (by have := hp.npw; omega_using [this])

theorem KR.saltBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem ((salt s₀).setWidth 64) (sl s₀) = bytesAt s₀.mem ((salt s₀).setWidth 64) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sa_o
    · exact hp.sa_s
    · exact hp.b_sa.symm) (by have := hp.nsa; omega_using [this])

end

/-- `d ← scratch + o`, while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR F s₀ s) {d : Reg} {o : Nat} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ =>
    k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, hk.ebp]

end VG.Proof.Pbkdf2.Whole.X86

end

end

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the prologue and the key

The prologue saves our caller's registers in `scratch` (`save_ok`, which is
`VG.Proof.Pbkdf2.Stream.X86.save_ok` for any amount of working space before the
save area); then the key is the password, or its digest if it is longer than a
block (`key_ok`): either gives the same `K₀` (`KeyAt`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK SavedRegs saveR InitArgs UpdArgs FinArgs init_frame upd_frame fin_frame
  saveList_ok saveMem_frameR saveMem_read saved_mem saved_pairwise zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_cmpi wp_test wp_addi wp_bswap wp_store)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey)

variable {F : Fns}

/-- Saving the registers, with `scratch` in `eax`: `VG.Proof.Pbkdf2.Stream.X86.save_ok`, for any `H.W`. -/
theorem save_ok (H : Hash) {s : State} {sc : BitVec 32} {L : Nat} (hax : s.gpr .eax = sc)
    (hsc : ⟨sc.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : sc.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [saveR H sc] s.mem s'.mem → SavedRegs H sc s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [Pbkdf2.Stream.X86.save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [hax]
    exact ⟨by omega_arith, ⟨_, hsc, contains_offset (by omega_arith) (by omega_arith)⟩⟩
  · rw [m, hax]
    exact saveMem_frameR _ _ _ _ (by omega_arith) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega_arith) p hp

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## The prologue -/

theorem prologue_ok : WP isa (.block F.prologue) s₀ (KR F s₀) := by
  have hL := end_le hz; have := layout (F := F)
  have hsc := sc_mem hp
  simp only [Fns.prologue, List.cons_append]
  refine wp_movm (a := argAddr s₀ 7) (argW rfl 7) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok F.L (sc := scr s₀) (L := F.L8) u₁.gpr (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 16 ≤ F.L8; omega_arith) hp.nsc fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine wp_mov fun s₃ u₃ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨by rw [u₃.rd, rd₂, u₁.rd], by rw [u₃.wr, wr₂, u₁.wr], by rw [u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₃.gpr, g₂, u₁.gpr]; rfl, ?_, ?_⟩
  · rw [u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [Pbkdf2.Stream.X86.savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)
  · rw [u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀ F, by simp, sv_sub hz⟩

/-! ## The stack and `scratch`, while `KR` holds -/

omit hz in
theorem stk48_sub {s : State} (hk : KR F s₀ s) : Region.Sub (Pbkdf2.Stream.X86.stk s) (stkR s₀) := by
  rw [Pbkdf2.Stream.X86.stk, hk.esp]; exact below_sub (by decide) hp.sp76

omit hz in
/-- A region of `scratch` is apart from the stack below `esp`. -/
theorem b76 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) :
    (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b48 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR s₀ F)) :
    (Pbkdf2.Stream.X86.stk s).Disjoint R :=
  (hp.b_s.sub_left (stk48_sub hp hk)).sub_right hR

omit hz in
/-- A part of `scratch`, as `Covers.of_sub` takes it. -/
theorem cov_part {s : State} (hk : KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_pw {s : State} (hk : KR F s₀ s) : Covers [pwR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

omit hz in
theorem cov_salt {s : State} (hk : KR F s₀ s) : Covers [saltR s₀] (s.rd ++ s.wr) :=
  Hmac.Generic.Common.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a password longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `edi ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)) s fun t =>
      KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stWO)]
  exact scr_ok hk fun s₁ u₁ => WP.block_nil ⟨hk.upd (by decide) u₁, u₁.gpr, u₁.mem⟩

omit hH in
theorem hk2_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    InitArgs (H := F.H) s .edi (dO s₀ F.stWO) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine ⟨hdi, by decide, by rw [hk.esp]; have := hp.sp76; omega_arith, ?_, ?_, ?_⟩
  · rw [ea]; exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk (hz.stWO_S)
  · rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
  · rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith

theorem hk2_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (F.H.callInit .edi) s fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine init_frame hH (hk2_args hp hz hk hdi) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, by rw [← ea]; exact r, a.cs _ (by decide)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact .inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩

omit hz hH in
/-- `update`'s arguments: the password. -/
theorem hk3_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (Fns.argM 1), .mov .edx (Fns.argM 0)]) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .esi = 0 ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 1 ∧ t.gpr .edx = pw s₀ ∧ t.mem = s.mem := by
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_arg hp k₂ (by decide) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨k₃.upd (by decide) u₄, ?_, ?_, ?_, ?_, u₄.gpr, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr]

theorem hk4_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = pw s₀) :
    UpdArgs hH s .esi .edi (dO s₀ F.stWO) (pw s₀) (scr s₀) 0 (pwl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 1).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cd := cov_pw hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.stWO_S)).symm
      d_st := by rw [ea]; exact hp.pw_s.sub_right (part_sub (hz.stWO_S))
      d_sc := hp.pw_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_d := hp.b_pw.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith
      nd := hp.npw
      nsc := by have := hp.nsc; omega_arith }

theorem hk4_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hsi : s.gpr .esi = 0)
    (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 1) (hdx : s.gpr .edx = pw s₀)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) ∧
        t.gpr .edi = s.gpr .edi := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  refine upd_frame hH (hk4_args hp hz hH hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, a.cs _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  · have := r [] (by rw [ea]; exact hr) rfl
    rwa [List.nil_append, ea, hk.pwBytes hp] at this

omit hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) :
    WP isa (.block (([.mov .eax (Fns.argM 1), .mov .ecx (.imm 0)] : List Instr) ++
      VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO)) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stWO ∧ t.gpr .eax = arg s₀ 1 ∧ t.gpr .ecx = 0 ∧
        t.gpr .edx = dO s₀ F.hkO ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO)]
  refine scr_ok k₂ fun s₃ u₃ => WP.block_nil ⟨k₂.upd (by decide) u₃, ?_, ?_, ?_, u₃.gpr, by
    rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem hk6_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO) :
    FinArgs hH s .edi (dO s₀ F.stWO) (dO s₀ F.hkO) (scr s₀) (arg s₀ 1) 0 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have eh := dO_addr hp (o := F.hkO) (hz.hkO_lt)
  exact
    { hst := hdi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_part hp hk (hz.hkO_F)
          · exact cov_low hp hk (by omega_arith)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega_arith)) (hz.stWO_S) (hz.hkO_F)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.stWO_S)).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega_arith) (hz.hkO_F)).symm
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_o := by rw [eh]; exact b48 hp hk (part_sub (hz.hkO_F))
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have := hp.nsc; omega_arith
      no := by rw [dO_toNat hp (hz.hkO_lt)]; have := hp.nsc; omega_arith
      nsc := by have := hp.nsc; omega_arith }

theorem hk6_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stWO) (hax : s.gpr .eax = arg s₀ 1)
    (hcx : s.gpr .ecx = 0) (hdx : s.gpr .edx = dO s₀ F.hkO)
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5)) s
      fun t => KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have eh := dO_addr hp (o := F.hkO) (hz.hkO_lt)
  refine fin_frame hH (hk6_args hp hz hH hk hdi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩
    · exact .inr ⟨_, _, by rw [eh], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (arg s₀ 1).isLt (by decide))
      (by rw [bytesAt_length, ← zero_append_ofNat (arg s₀ 1).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp hz hH in
theorem hk7_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.hkO ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ⟨(hk.upd (by decide) u₁).upd (by decide) u₂,
    by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr, by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.hashKey s fun t => KR F s₀ t ∧ t.gpr .edx = dO s₀ F.hkO ∧ t.gpr .ecx = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.hashKey
  refine WP.seq (WP.mono (hk1_ok hk) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  have d₂ : s₂.gpr .edi = dO s₀ F.stWO := e₂.trans d₁
  refine WP.seq (WP.mono (hk3_ok hp k₂ d₂) fun s₃ ⟨k₃, d₃, i₃, a₃, c₃, x₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ d₃ i₃ a₃ c₃ x₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, r₄, e₄⟩ => ?_)
  have d₄ : s₄.gpr .edi = dO s₀ F.stWO := e₄.trans d₃
  refine WP.seq (WP.mono (hk5_ok hp k₄ d₄) fun s₅ ⟨k₅, d₅, a₅, c₅, x₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ d₅ a₅ c₅ x₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

/-! ## The key -/

omit hH in
theorem cmp_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => KR F s₀ t ∧ t.gpr .ecx = arg s₀ 1 ∧
      t.cf = some (decide (pwl s₀ < F.H.B + 1)) ∧ t.mem = s.mem := by
  have := hz.B
  refine wp_arg hp hk (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
  refine ⟨(hk.upd (by decide) u₁).same f₂.rd f₂.wr (fun r _ => by rw [f₂.gpr]) f₂.mem, by rw [f₂.gpr, u₁.gpr], ?_,
    by rw [f₂.mem, u₁.mem]⟩
  rw [c₂, u₁.gpr, toNat_ofNat32 (by omega_arith)]

omit hp hz in
theorem hash_len {k : List Byte} {m : Mem} {p : Addr} (h : bytesAt m p F.H.D = hH.SH.H.hash k) :
    (hH.SH.H.hash k).length = F.H.D := by
  rw [← h, bytesAt_length]

omit hp in
/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : F.H.B < k.length) (hl : (hH.SH.H.hash k).length = F.H.D) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB; have := hz.DB
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ F.H.B < F.H.D by omega_arith))]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if pwl s₀ < F.H.B + 1 then pw s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if pwl s₀ < F.H.B + 1 then pwl s₀ else F.H.D

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : KR F s₀ s) :
    WP isa F.key s fun t => KR F s₀ t ∧ t.gpr .edx = kp F s₀ ∧ t.gpr .ecx = BitVec.ofNat 32 (kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem ((kp F s₀).setWidth 64) (kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (cmp_ok hp hz hk) fun s₁ ⟨k₁, c₁, f₁, _⟩ => ?_)
  refine WP.ite (decide (F.H.B + 1 ≤ pwl s₀)) (by
    show (s₁.cf.map (!·)) = _
    rw [f₁]; simp only [Option.map_some, ← decide_not, Nat.not_lt])
    (fun hT => ?_) fun hF => ?_
  · have hlt : ¬ pwl s₀ < F.H.B + 1 := by have := of_decide_eq_true hT; omega_arith
    simp only [kp, kl, hlt, ↓reduceIte]
    refine WP.mono (hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D
    rw [show (dO s₀ F.hkO).setWidth 64 = A s₀ F.hkO from dO_addr hp (by have := end_le hz; have := layout (F := F); omega_arith),
      b, blockKey_hash hz hH (by rw [bytesAt_length]; omega_arith) (hash_len hH b)]
  · have hlt : pwl s₀ < F.H.B + 1 := by have := of_decide_eq_false hF; omega_arith
    simp only [kp, kl, hlt, ↓reduceIte]
    refine wp_arg hp k₁ (by decide) fun s₂ u₂ => WP.block_nil ⟨k₁.upd (by decide) u₂, u₂.gpr, ?_, ?_⟩
    · rw [u₂.other _ (by decide), c₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [u₂.mem, k₁.pwBytes hp]

end

/-! ## Where the key is -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- The key's region is the password, or the hashed password in `scratch`. -/
theorem key_cases : (kp F s₀ = pw s₀ ∧ kl F s₀ = pwl s₀ ∧ pwl s₀ ≤ F.H.B) ∨
    ((kp F s₀).setWidth 64 = A s₀ F.hkO ∧ kl F s₀ = F.H.D) := by
  by_cases h : pwl s₀ < F.H.B + 1
  · exact .inl ⟨by simp [kp, h], by simp [kl, h], by omega_arith⟩
  · refine .inr ⟨?_, by simp [kl, h]⟩
    simp only [kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega_arith)

theorem kl_le : kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega_arith

theorem key_toNat : (kp F s₀).toNat + kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : pwl s₀ < F.H.B + 1
  · simp only [kp, kl, h, ↓reduceIte]; exact hp.npw
  · simp only [kp, kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp (hz.hkO_lt)]
    have := hp.nsc; omega_arith

/-- The key is apart from the parts of `scratch` after the hashed password,
from the working space, and from the stack below `esp`. -/
theorem key_disj {R : Region} (hR : Region.Sub R (scR s₀ F))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ R := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.pw_s.sub_right hR
  · rw [h, h']; exact hd.symm

theorem key_stk {s : State} (hk : KR F s₀ s) : (stk s).Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ := by
  rw [hk.stkE]
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_pw
  · rw [h, h']; exact hp.b_s.sub_right (part_sub (by have := end_le hz; have := layout (F := F); have := hz.D; omega_arith))

theorem key_cov {s : State} (hk : KR F s₀ s) : Covers [⟨(kp F s₀).setWidth 64, kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact cov_pw hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.hkO) (n := F.H.D)
        (by have := end_le hz; have := layout (F := F); have := hz.D; omega_arith)
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

end VG.Proof.Pbkdf2.Whole.X86

end

end

/-! ### `Pbkdf2.Whole.X86.Setup`, which only this module used -/

section

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: HMAC's states for the key, and the salt

HMAC's `init` makes the key's inner and outer states; the inner one is copied
and absorbs the salt (`setup_ok`), which gives the three states every block
starts from (`States`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK UpdArgs upd_frame CopyInv Copied copy_ok cclob)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad)

variable {F : Fns}

/-- `K₀`, the password padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem ((salt s₀).setWidth 64) (sl s₀)

/-- The key's states, and the inner one after the salt. -/
structure States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop where
  st0 : hF.hH.SH.Repr m (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad)
  st1 : hF.hH.SH.Repr m (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)
  stS : hF.hH.SH.Repr m (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)

/-- The representation is kept by what writes elsewhere. -/
theorem repr_keep (hH : HashOK F.H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, F.H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, F.H.S⟩) hd (by show F.H.S ≤ 2 ^ 64; have := hH.hSB; omega_arith) hi) hr

/-- The three states are kept by what writes elsewhere: after them in `scratch`. -/
theorem States.keep {hF : FnsOK F} {s₀ : State} (hz : Sizes F) {m m' : Mem} (h : States hF s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (3 * F.H.S)) r) :
    States hF s₀ m' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have sub : ∀ o, F.st0O ≤ o → o + F.H.S ≤ F.st0O + 3 * F.H.S →
      Region.Sub (sR s₀ o F.H.S) (sR s₀ F.st0O (3 * F.H.S)) := fun o h₁ h₂ =>
    Offset.sub _ h₁ h₂
  refine ⟨repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.st0,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.st1,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega_arith) (by omega_arith))) h.stS⟩

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- A copy of `n > 0` bytes within `scratch`, after the save area. -/
theorem copy_part_ok {s : State} (hk : KR F s₀ s) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ F.L8)
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 16 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .ebp a .ebp b n) s fun t => KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = writeBytes s.mem (A s₀ b) (bytesAt s.mem (A s₀ a) n) := by
  have hL := L8_le hz; have := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .ebp) (dst := .ebp) (by decide) (by decide) hn (by omega_arith)
    (by rw [hk.ebp]; omega_arith) (by rw [hk.ebp]; omega_arith)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [hk.ebp]; exact part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.ebp] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr (fun r hr => c.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide))
    hb' hb f, c.other, c.mem⟩

omit hp hz in
/-- After such a copy, the bytes at `b` are those at `a`. -/
theorem copied_byte {m : Mem} {a b n : Nat} (hn : n ≤ 2 ^ 32) (i : Nat) (hi : i < n) :
    writeBytes m (A s₀ b) (bytesAt m (A s₀ a) n) (A s₀ b + BitVec.ofNat 64 i) = m (A s₀ a + BitVec.ofNat 64 i) := by
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith), bytesAt_getD' _ _ hi]

end

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  edx : s.gpr .edx = kp F s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem ((kp F s₀).setWidth 64) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KR F s₀ s) : WP isa F.key s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp hz in
theorem su1_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.st0O ++ VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)) s
      fun t => Keyed hF s₀ t ∧ t.gpr .edi = dO s₀ F.st0O ∧ t.gpr .esi = dO s₀ F.st1O := by
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have k₁ := h.kr.upd (by decide) u₁
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)]
  refine scr_ok k₁ fun s₂ u₂ => WP.block_nil ⟨⟨k₁.upd (by decide) u₂, ?_, ?_, ?_⟩, ?_, u₂.gpr⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₂.mem, u₁.mem]; exact h.k0
  · rw [u₂.other _ (by decide), u₁.gpr]

theorem su2_args {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    key_disj hp hz (part_sub (by omega_arith)) (part_disj hz (Or.inl h₁) (by omega_arith) (hz.hkO_D))
  have kls : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega_arith)) (low_disj hz (by omega_arith) (hz.hkO_D))
  exact
    { edi := hdi
      esi := hsi
      edx := h.edx
      ecx := h.ecx
      ebp := hk.ebp
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega_arith
      sp := by rw [hk.esp]; exact hp.sp76
      cr := key_cov hp hz hk
      cw := by
        rw [hS, e0, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.st0O_S)
          · exact cov_part hp hk (hz.st1O_S)
          · exact cov_low hp hk (by omega_arith)
      i_o := by rw [hS, e0, e1]; exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.st1O_S)
      i_k := by rw [hS, e0]; exact (kd _ _ (by omega_arith) (by omega_arith)).symm
      i_s := by rw [hS, e0]; exact (low_disj hz (by omega_arith) (hz.st0O_S)).symm
      o_k := by rw [hS, e1]; exact (kd _ _ (by omega_arith) (by omega_arith)).symm
      o_s := by rw [hS, e1]; exact (low_disj hz (by omega_arith) (hz.st1O_S)).symm
      k_s := kls
      b_i := by rw [hS, e0]; exact b76 hp hk (part_sub (hz.st0O_S))
      b_o := by rw [hS, e1]; exact b76 hp hk (part_sub (hz.st1O_S))
      b_k := key_stk hp hz hk
      b_s := b76 hp hk (low_sub (by omega_arith))
      ni := by rw [hS, dO_toNat hp (hz.st0O_lt)]; have := hp.nsc; omega_arith
      no := by rw [hS, dO_toNat hp (hz.st1O_lt)]; have := hp.nsc; omega_arith
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega_arith }

theorem su2_ok {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    WP isa (.frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax hi5.length)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  refine hi_frame hF.hi hF.hiSp hF.hiSU (su2_args hp hz hF h hdi hsi) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [e0, hS], by omega_arith, by omega_arith⟩
    · exact .inr ⟨_, _, by rw [e1, hS], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  · rw [h.k0, e0] at r0; exact r0
  · rw [h.k0, e1] at r1; exact r1

omit hF in
theorem K0_length (hF : FnsOK F) {s : State} (h : Keyed hF s₀ s) : (K0 hF s₀).length = F.H.B := by
  have := kl_le hp hz
  rw [← h.k0]
  simp only [blockKey, hF.hH.hB, bytesAt_length, show ¬ F.H.B < kl F s₀ by omega_arith, ↓reduceIte,
    List.length_append, List.length_replicate]
  omega_arith

/-- The key's inner state, copied for the salt. -/
theorem su3_ok {s : State} (hk : KR F s₀ s) (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)) :
    WP isa (copy .ebp F.st0O .ebp F.stSO F.H.S) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have hL := L8_le hz
  refine WP.mono (copy_part_ok hp hz hk hz.S.1 (hz.st0O_S) (hz.stSO_S) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, repr_keep hF.hH f (fun r hr => ?_) r0, repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.stSO_S)
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega_arith)) (hz.st1O_S) (hz.stSO_S)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact copied_byte (by omega_arith) i hi

omit hz hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stSO ++ ([.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stSO ∧ t.gpr .esi = BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 3 ∧ t.gpr .edx = salt s₀ ∧ t.mem = s.mem := by
  refine scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have k₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => ?_
  have k₄ := k₃.upd (by decide) u₄
  refine wp_arg hp k₄ (by decide) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨k₄.upd (by decide) u₅, ?_, ?_, ?_, ?_, u₅.gpr, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

omit hF in
/-- The salt is apart from `scratch`, so `B + salt_len` does not wrap around. -/
theorem salt_fit : F.H.B + 4 + sl s₀ < 2 ^ 32 := by
  have h₁ : (saltR s₀).base.toNat + (saltR s₀).len ≤ 2 ^ 32 := by
    show ((salt s₀).setWidth 64).toNat + sl s₀ ≤ _; rw [toNat_setWidth64]; exact hp.nsa
  have h₂ : (scR s₀ F).base.toNat + (scR s₀ F).len ≤ 2 ^ 32 := by
    show ((scr s₀).setWidth 64).toNat + F.L8 ≤ _; rw [toNat_setWidth64]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have := hz.B; have := hz.S; have := hz.BS
  omega_arith

theorem su5_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stSO) (salt s₀) (scr s₀) (BitVec.ofNat 32 F.H.B) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega_arith)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 3).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega_arith
      cd := cov_salt hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stSO_S)
          · exact cov_low hp hk (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega_arith) (hz.stSO_S)).symm
      d_st := by rw [ea]; exact hp.sa_s.sub_right (part_sub (hz.stSO_S))
      d_sc := hp.sa_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stSO_S))
      b_d := hp.b_sa.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp (by omega_arith)]; have := hp.nsc; omega_arith
      nd := hp.nsa
      nsc := by have := hp.nsc; omega_arith }

theorem su5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) (hkl : (K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega_arith)
  refine upd_frame hF.hH (su5_args hp hz hF hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_arith⟩
  all_goals have f := a.frame
  all_goals rw [ea] at f
  · refine repr_keep hF.hH f (fun r hr => ?_) r0
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega_arith)) (hz.st0O_S) (hz.stSO_S)
    · exact low_disj hz (by omega_arith) (hz.st0O_S) |>.symm
    · exact (b48 hp hk (part_sub (hz.st0O_S))).symm
  · refine repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega_arith)) (hz.st1O_S) (hz.stSO_S)
    · exact low_disj hz (by omega_arith) (hz.st1O_S) |>.symm
    · exact (b48 hp hk (part_sub (hz.st1O_S))).symm
  · have := r (xorPad (K0 hF s₀) ipad) (by rw [ea]; exact rS) (by
      rw [xorPad_length, hkl, Pbkdf2.Stream.X86.zero_append_ofNat (by have := hz.B; omega_arith)])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa F.setup s fun t => KR F s₀ t ∧ States hF s₀ t.mem ∧ (K0 hF s₀).length = F.H.B := by
  have hkl := K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (su1_ok hF h) fun s₁ ⟨k₁, d₁, i₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hF k₁ d₁ i₁) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (su4_ok hp k₃) fun s₄ ⟨k₄, d₄, i₄, a₄, c₄, x₄, m₄⟩ => ?_)
  exact WP.mono (su5_ok hp hz hF k₄ d₄ i₄ a₄ c₄ x₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.X86

end

end


/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: a block of the output, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `ebx` is `done k`, and `scratch` holds `INT (k + 1)`,
byte-reversed. A step copies the salted inner state into the working state,
absorbs `INT (k + 1)` into it (`update`) and computes `U₁` with HMAC's
`finalize`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK UpdArgs upd_frame cclob zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_addi wp_store wp_bswap wp_test)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

variable {F : Fns}

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hF : FnsOK F) (s₀ : State) : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (K0 hF s₀)

/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (hF : FnsOK F) (s₀ : State) (k : Nat) : List Byte := Whole.G (prf hF s₀) (saltB s₀) (cc s₀) k
abbrev Tk (hF : FnsOK F) (s₀ : State) (i : Nat) : List Byte := Whole.Tb (prf hF s₀) (saltB s₀) (cc s₀) i
abbrev nbk (F : Fns) (s₀ : State) : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (F : Fns) (s₀ : State) (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR F s₀ s
  st : States hF s₀ s.mem
  k0l : (K0 hF s₀).length = F.H.B
  ebx : s.gpr .ebx = BitVec.ofNat 32 (dn F s₀ k)
  intW : s.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem ((out s₀).setWidth 64) (dn F s₀ k) = (Gk hF s₀ k).take (dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.esp, .ebp, .ebx]

/-- Where a step writes, before it copies `T` out: the working space, or
the parts of `scratch` from the working state up to `INT (i)`. -/
def Wks (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨ ∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hp in
theorem Wks.disj {r : Region} (h : Wks F s₀ r) :
    (svR F s₀).Disjoint r ∧ Region.Sub r (scR s₀ F) ∧ (sR s₀ F.st0O (3 * F.H.S)).Disjoint r ∧
      (sR s₀ F.intO 4).Disjoint r := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  rcases h with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
  · exact ⟨sv_low hz hk, low_sub (by omega_using [hl, he, hk]), (low_disj hz (by omega_using [hl, hk]) (hz.st0O_3S)).symm,
      (low_disj hz (by omega_using [hl, hk]) (end_le hz)).symm⟩
  · exact ⟨sv_disj hz (by omega_using [hl, h₁]) (by omega_using [h₂, he]), part_sub (by omega_using [he, h₂]),
      part_disj hz (Or.inl (by omega_using [hl, h₁])) (hz.st0O_3S) (by omega_using [he, h₂]), part_disj hz (Or.inr (by omega_using [h₂])) (end_le hz) (by omega_using [he, h₂])⟩

/-- `Inv` survives writes where a step writes, and to the stack below `esp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wks F s₀ r ∨ r = stkR s₀) : Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  have hsb : (stkR s₀).Disjoint (scR s₀ F) := hp.b_s
  refine ⟨h.kr.keep hrd hwr (fun r hr => hg r (by simp only [List.mem_cons] at hr ⊢; grind)) hf
    (fun r hr => ?_) (fun r hr => ?_), h.st.keep hz hf (fun r hr => ?_), h.k0l, by rw [hg _ (by simp), h.ebx],
    ?_, h.glen, ?_⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).1
    · exact (hsb.sub_right (sv_sub hz)).symm
  · rcases hw r hr with hw | rfl
    · exact ⟨_, by simp, (hw.disj hz).2.1⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.1
    · exact (hsb.sub_right (part_sub (hz.st0O_3S))).symm
  · rw [← h.intW]
    refine hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.2
    · exact (hsb.sub_right (part_sub (end_le hz))).symm
  · rw [← h.outB]
    have osub : Region.Sub ⟨(out s₀).setWidth 64, dn F s₀ k⟩ (outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have hp_no := hp.no; omega_using [hp_no, h1])
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.upd {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {d : Reg} (hd : d ∉ iregs) {v : BitVec 32}
    (u : Upd s s' d v) : Inv hF s₀ k s' :=
  h.keep hp hz u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

theorem Inv.same {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, Wks F s₀ r) : Inv hF s₀ k s' := by
  have f := ha.frame
  rw [h.kr.stkE] at f
  refine h.keep hp hz ha.rd ha.wr (fun r hr => ha.cs r (by simp only [List.mem_cons] at hr ⊢; simp [calleeSaved]; grind))
    f fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hw r hr)
  · simp only [List.mem_singleton] at hr; exact .inr hr

/-! ## The loop's start -/

omit hp hz in
theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

omit hz in
theorem ea_scr {s : State} (hk : KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    s.ea (at_ .ebp o) = A s₀ o := by
  rw [show s.ea (at_ .ebp o) = (dO s₀ o).setWidth 64 by
    show (s.gpr .ebp + BitVec.ofNat 32 o).setWidth 64 = _; rw [hk.ebp]]
  exact dO_addr hp ho

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : KR F s₀ s) (hst : States hF s₀ s.mem) (hkl : (K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => Inv hF s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_D := hz.D
  unfold Fns.loopInit
  refine wp_movi fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (a := A s₀ F.intO) (ea_scr hp ((hk.upd (by decide) u₁).upd (by decide) u₂) (hz.intO_lt))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (end_le hz)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (fun r hr => by
      rw [m₃.gpr, u₂.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all),
        u₁.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all)])
    (by omega_using [hl]) (end_le hz) f₃
  refine wp_movi fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (by decide) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st0O_3S) (end_le hz)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, Pbkdf2.Stream.X86.test_z]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (copy .ebp F.stSO .ebp F.stWO F.H.S) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D
  refine WP.mono (copy_part_ok hp hz h.kr hz.S.1 (hz.stSO_S) (hz.stWO_S) (by omega_using [hl]) (Or.inl (by omega_using [hl])))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega_using [hl]⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact copied_byte (by omega_using [hz_S]) i hi

/-- `update`'s arguments: the working state, `B + salt_len`, `INT (i)`. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edi = dO s₀ F.stWO ∧
      t.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = BitVec.ofNat 32 4 ∧
      t.gpr .edx = dO s₀ F.intO ∧ t.mem = s.mem := by
  simp only [Fns.updArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine wp_arg hp i₁.kr (by decide) fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have i₅ := (((i₁.upd hp hz (by decide) u₂).upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz
    (by decide) u₅
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.intO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b3_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stWO) (dO s₀ F.intO) (scr s₀) (arg s₀ 3 + BitVec.ofNat 32 F.H.B) 4 := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have ei := dO_addr hp (o := F.intO) (hz.intO_lt)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := by decide
      sp48 := by rw [hk.esp]; have hp_sp76 := hp.sp76; omega_using [hp_sp76]
      cd := by
        rw [ei]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.intO) (n := 4) (end_le hz)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_low hp hk (by omega_using [hl, he, hz_W, this])
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega_using [hl, hz_W, this]) (hz.stWO_S)).symm
      d_st := by rw [ei, ea]; exact part_disj hz (Or.inr (hz.stWO_S_intO)) (end_le hz) (hz.stWO_S)
      d_sc := by rw [ei]; exact (low_disj hz (k := hF.hH.Wb) (by omega_using [hl, hz_W, this]) (end_le hz)).symm
      b_st := by rw [ea]; exact b48 hp hk (part_sub (hz.stWO_S))
      b_d := by rw [ei]; exact b48 hp hk (part_sub (end_le hz))
      b_sc := b48 hp hk (low_sub (by omega_using [hl, he, hz_W, this]))
      nst := by rw [dO_toNat hp (hz.stWO_lt)]; have hp_nsc := hp.nsc; omega_using [hl, he, hp_nsc]
      nd := by rw [dO_toNat hp (hz.intO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he]
      nsc := by have hp_nsc := hp.nsc; omega_using [hl, he, hz_W, this, hp_nsc] }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have ei := dO_addr hp (o := F.intO) (hz.intO_lt)
  have hsf := salt_fit hp hz
  refine upd_frame hF.hH (b3_args hp hz h hdi hsi hax hcx hdx) fun s' a r => ⟨h.after hp hz (After.of_hmac (by
    rw [h.kr.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega_using [hl]⟩
    · exact .inl ⟨_, rfl, by omega_using [this, hz_W]⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [List.length_append, xorPad_length, h.k0l, bytesAt_length,
        show arg s₀ 3 + BitVec.ofNat 32 F.H.B = BitVec.ofNat 32 (F.H.B + sl s₀) by
          rw [Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        zero_append_ofNat (by omega_using [hsf])])
    rwa [ea, ei, Whole.bytes_rev_int h.intW] at this

/-! ## A step: `U₁` -/

omit hp hz in
theorem FnsOK.reprOK (hF : FnsOK F) : ReprOK hF.hH.SH := fun m m' p q msg hb =>
  hF.hH.repr m m' p q msg (fun i hi => hb i (by rw [hF.hH.hS]; exact hi))

omit hp hz in
theorem add_ofNat_eq (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := h
  omega_using []

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edx = dO s₀ F.stWO ∧
      t.gpr .esi = dO s₀ F.st1O ∧ t.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧ t.gpr .ecx = 0 ∧
      t.gpr .edi = dO s₀ F.uO ∧ t.mem = s.mem := by
  simp only [Fns.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have i₅ := ((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.uO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4)) 0
      (dO s₀ F.uO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have eu := dO_addr hp (o := F.uO) (hz.uO_lt)
  exact
    { edx := hdx
      esi := hsi
      eax := hax
      ecx := hcx
      edi := hdi
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
      cr := by
        rw [hS, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st1O) (n := F.H.S) (hz.st1O_S)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hS, hD, ew, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (hz.stWO_S)
          · exact cov_part hp hk (hz.uO_D)
          · exact cov_low hp hk (by omega_using [hF_hWf, he, hl])
      i_u := by rw [hS, ew, e1]; exact part_disj hz (Or.inr (by omega_using [hl])) (hz.stWO_S) (hz.st1O_S)
      i_o := by rw [hS, hD, ew, eu]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.stWO_S) (hz.uO_D)
      i_s := by rw [hS, ew]; exact (low_disj hz (by omega_using [hl, hF_hWf]) (hz.stWO_S)).symm
      u_o := by rw [hS, hD, e1, eu]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st1O_S) (hz.uO_D)
      u_s := by rw [hS, e1]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (hz.st1O_S)).symm
      o_s := by rw [hD, eu]; exact (low_disj hz (by omega_using [hF_hWf, hl]) (hz.uO_D)).symm
      b_i := by rw [hS, ew]; exact b76 hp hk (part_sub (hz.stWO_S))
      b_u := by rw [hS, e1]; exact b76 hp hk (part_sub (hz.st1O_S))
      b_o := by rw [hD, eu]; exact b76 hp hk (part_sub (hz.uO_D))
      b_s := b76 hp hk (low_sub (by omega_using [hl, he, hF_hWf]))
      ni := by rw [hS, dO_toNat hp (hz.stWO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hS, dO_toNat hp (hz.st1O_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      no := by rw [hD, dO_toNat hp (hz.uO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWf, he, hl] }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push hf6) (.call F.hfN F.hfC) (.pop .eax hf6.length)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  have hF_hWf := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (hz.stWO_lt)
  have e1 := dO_addr hp (o := F.st1O) (hz.st1O_lt)
  have eu := dO_addr hp (o := F.uO) (hz.uO_lt)
  have hsf := salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) hF.hf hF.hfSp hF.hfSU (b5_args hp hz h hdx hsi hax hcx hdi)
    fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ew, hS], Nat.le_refl _, by omega_using [hl]⟩
    · exact .inr ⟨_, _, by rw [eu, hD], by omega_using [hl], by omega_using [hl]⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWf]⟩
  · have := post (K0 hF s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) (by rw [h.k0l, hB])
      (by rw [h.k0l, List.length_append, bytesAt_length]; simp only [Spec.Pbkdf2.int, List.length_cons,
        List.length_nil]; omega_using [hsf])
      (by rw [ew, ← List.append_assoc]; exact hr)
      (by
        rw [List.length_append, bytesAt_length, hB,
          show arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) = BitVec.ofNat 32 (F.H.B + (sl s₀ + 4)) by
            rw [add_ofNat_eq _ (by have : sl s₀ = (arg s₀ 3).toNat := rfl; omega_using [this, hsf]),
              show (arg s₀ 3).toNat + (F.H.B + 4) = F.H.B + (sl s₀ + 4) by
                have : sl s₀ = (arg s₀ 3).toNat := rfl; omega_using [this]],
          zero_append_ofNat (by omega_using [hsf])]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.X86

end

end

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the rest of a block, the loop, and `pbkdf2`

A step copies `U₁` into `T`, runs `iterate` for the rest of the chain, copies
as much of `T` as the output still needs (`copyR_ok`, a byte copy of a length
in a register), and moves on to the next block; after the last one, `out`
holds the derived key.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK cclob count_loop nm ea_at addr3 ofNat_succ32)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_sub wp_subi wp_cmp wp_cmpi
  wp_store wp_bswap wp_movzx8 wp_store8 sub_beq sub_ofNat)
open VG.Proof.Hmac.Generic.Common (bytes_keep writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

/-! ## A byte copy of a length in a register -/

/-- After `k` bytes of a copy from `A` to `B`. -/
structure CopyRInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The loop copying `n = esi > 0` bytes from `[ebp + so]` to `[edi]`, with
`ecx` the index. -/
theorem copyR_ok {so n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State} (hsi : s.gpr .esi = BitVec.ofNat 32 n)
    (hcx : s.gpr .ecx = 0)
    (hsw : (s.gpr .ebp).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr .edi).toNat + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so, n⟩ ⟨(s.gpr .edi).setWidth 64, n⟩) :
    WP isa (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax so),
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store8 (at_ .eax 0) .dl,
      .alu .add .ecx (.imm 1), .alu .cmp .ecx (.reg .esi)]) .ne) s
      (CopyRInv s ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so) ((s.gpr .edi).setWidth 64) n) := by
  generalize eA : (s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so = A at hin hsep ⊢
  generalize eB : (s.gpr .edi).setWidth 64 = B at hout hsep ⊢
  obtain i0 : CopyRInv s A B 0 s :=
    ⟨rfl, rfl, fun _ _ => rfl, hcx, by rw [bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine count_loop hn (CopyRInv s A B) (fun k hk t h => ?_) i0
  obtain gb := h.other .ebp (by decide)
  obtain gd := h.other .edi (by decide)
  obtain gs := h.other .esi (by decide)
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, addr3 (by omega_arith), eA])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gd, h.ecx,
      addr3 (by omega_arith), eB]
        exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₆ m₆ => ?_
  refine wp_addi fun t₇ u₇ => wp_cmp fun t₈ f₈ _ z₈ => WP.block_nil ?_
  obtain h7 : t₇.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, ofNat_succ32]
  refine ⟨⟨by rw [f₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₈.gpr, u₇.other r (nm hr .ecx), m₆.gpr, u₅.other r (nm hr .eax), u₄.other r (nm hr .eax),
        u₃.other r (nm hr .edx), u₂.other r (nm hr .eax), u₁.other r (nm hr .eax), h.other r hr],
    by rw [f₈.gpr, h7], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    obtain v : (t₅.gpr .edx).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_arith), ↓reduceIte]
      ext i hi; simp
    obtain e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_using [hk, hn'])
    rw [hl] at e'
    rw [f₈.mem, u₇.mem, m₆.mem, show Reg8.dl.reg = .edx from rfl, v, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      h.mem, bytesAt_snoc', e']
  · rw [z₈, h7, u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, hsi, sub_beq (by omega_arith) hn']

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## A step: `T`, from `U₁` and `iterate` -/

/-- `T ← U₁`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte} (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = u) :
    WP isa (copy .ebp F.uO .ebp F.tO F.H.D) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = u ∧ bytesAt t.mem (A s₀ F.tO) F.H.D = u := by
  obtain hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D
  refine WP.mono (copy_part_ok hp hz h.kr hz.D.1 (hz.uO_D) (hz.tO_D) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨kt, g, m⟩ => ?_
  obtain f : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, by omega_arith, by omega_arith⟩), ?_, ?_⟩
  · rw [bytes_keep f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega_arith)) (hz.uO_D) (hz.tO_D))
      (by omega_using [hz_D])]
    exact hu
  · rw [m, Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega_using [hz_D])]
    exact hu

/-- `iterate`'s arguments: the key's states, `U`, `c - 1` and `T`. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .esi = dO s₀ F.st0O ∧
      t.gpr .eax = dO s₀ F.uO ∧ t.gpr .ecx = arg s₀ 4 - 1 ∧ t.gpr .edx = dO s₀ F.tO ∧ t.mem = s.mem := by
  simp only [Fns.iterArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  obtain i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  obtain i₄ := (i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.tO)]
  refine scr_ok i₄.kr fun s₅ u₅ => WP.block_nil ⟨i₄.upd hp hz (by decide) u₅, ?_, ?_, ?_, u₅.gpr, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO) :
    ItArgs hF.hH.SH hF.Wt s (dO s₀ F.st0O) (dO s₀ F.uO) (arg s₀ 4 - 1) (dO s₀ F.tO) (scr s₀) := by
  obtain hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  obtain hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  obtain e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  obtain eu := dO_addr hp (o := F.uO) (hz.uO_lt)
  obtain et := dO_addr hp (o := F.tO) (hz.tO_lt)
  exact
    { esi := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
      cr := by
        rw [hS, hD, e0, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st0O) (n := 2 * F.H.S) (hz.st0O_2S)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.uO) (n := F.H.D) (hz.uO_D)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hD, et]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (hz.tO_D)
          · exact cov_low hp hk (by omega_using [hF_hWt, he, hl])
      k_t := by rw [hS, hD, e0, et]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st0O_2S) (hz.tO_D)
      k_s := by rw [hS, e0]; exact (low_disj hz (by omega_using [hF_hWt, hl]) (hz.st0O_2S)).symm
      u_t := by rw [hD, eu, et]; exact part_disj hz (Or.inl (by omega_using [hl])) (hz.uO_D) (hz.tO_D)
      u_s := by rw [hD, eu]; exact (low_disj hz (by omega_arith) (hz.uO_D)).symm
      t_s := by rw [hD, et]; exact (low_disj hz (by omega_using [hF_hWt, hl]) (hz.tO_D)).symm
      b_k := by rw [hS, e0]; exact b76 hp hk (part_sub (hz.st0O_2S))
      b_u := by rw [hD, eu]; exact b76 hp hk (part_sub (hz.uO_D))
      b_t := by rw [hD, et]; exact b76 hp hk (part_sub (hz.tO_D))
      b_s := b76 hp hk (low_sub (by omega_arith))
      nk := by rw [hS, dO_toNat hp (hz.st0O_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nu := by rw [hD, dO_toNat hp (hz.uO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nt := by rw [hD, dO_toNat hp (hz.tO_lt)]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl]
      nsc := by have hp_nsc := hp.nsc; omega_using [hp_nsc, hF_hWt, he, hl] }

/-- `iterate`: `T_{k + 1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO)
    (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push it5) (.call F.itN F.itC) (.pop .eax it5.length)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1) := by
  obtain hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hz_D := hz.D; have hz_W := hz.W
  obtain hF_hWt := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  obtain e0 := dO_addr hp (o := F.st0O) (hz.st0O_lt)
  obtain eu := dO_addr hp (o := F.uO) (hz.uO_lt)
  obtain et := dO_addr hp (o := F.tO) (hz.tO_lt)
  refine it_frame (FnsOK.reprOK hF) (by rw [hS]; omega_using [hz_S]) (by rw [hD]; omega_using [hz_D]) hF.it hF.itSp hF.itSU
    (b8_args hp hz h hsi hax hcx hdx) fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [et, hD], by omega_using [hl], by omega_arith⟩
    · exact .inl ⟨_, rfl, by omega_using [hF_hWt]⟩
  · have := post (K0 hF s₀) (by rw [h.k0l, hB]) (by rw [e0]; exact h.st.st0)
      (by rw [e0, hS, Hmac.Generic.Common.add_ofNat_add]; exact h.st.st1)
    rw [et, hD, eu, hu, ht] at this
    rw [this]
    have hc := hp.c0
    rw [show (arg s₀ 4 - 1).toNat = cc s₀ - 1 by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ (arg s₀ 4).toNat; exact hc)]; rfl]
    rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem arg_ofNat (i : Nat) : arg s₀ i = BitVec.ofNat 32 (arg s₀ i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {k : Nat} (hk : k * F.H.D < ol s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧
      t.gpr .ecx = BitVec.ofNat 32 (min (ol s₀ - k * F.H.D) F.H.D) ∧ t.mem = s.mem := by
  obtain hD := hz.D; have hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  obtain hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega_arith
  unfold Fns.outLen
  refine WP.seq (wp_arg hp h.kr (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmpi fun s₃ f₃ c₃ _ =>
    WP.block_nil ?_)
  obtain i₃ := ((h.upd hp hz (by decide) u₁).upd hp hz (by decide) u₂).same hp hz f₃.rd f₃.wr
    (fun r _ => by rw [f₃.gpr]) f₃.mem
  obtain e₃ : s₃.gpr .ecx = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by
    rw [f₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.ebx, hdn, arg_ofNat 6,
      sub_ofNat (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega_arith)]
  obtain m₃ : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  obtain cf : s₃.cf = some (decide (ol s₀ - k * F.H.D < F.H.D)) := by
    rw [c₃, ← f₃.gpr, e₃, toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by show s₃.cf = _; rw [cf]) (fun hT => WP.block_nil ?_)
    fun hF' => wp_movi fun s₄ u₄ => WP.block_nil ⟨i₃.upd hp hz (by decide) u₄, ?_, by rw [u₄.mem, m₃]⟩
  · have : ol s₀ - k * F.H.D < F.H.D := of_decide_eq_true hT
    exact ⟨i₃, by rw [e₃, Nat.min_eq_left (Nat.le_of_lt this)], m₃⟩
  · have : ¬ ol s₀ - k * F.H.D < F.H.D := of_decide_eq_false hF'
    rw [u₄.gpr, Nat.min_eq_right (by omega_arith)]

/-- Copying `n` bytes of `T` to `out` after the `k D` written. -/
theorem outLoop_ok {k n : Nat} (hn : 0 < n) (hkn : k * F.H.D + n ≤ ol s₀) (hnD : n ≤ F.H.D) {s : State}
    (h : Inv hF s₀ k s) (hcx : s.gpr .ecx = BitVec.ofNat 32 n) (hkD : k * F.H.D < ol s₀) :
    WP isa F.outLoop s fun t => KR F s₀ t ∧ t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
        (bytesAt s.mem (A s₀ F.tO) n) := by
  obtain hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D
  obtain hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  obtain hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega_using [hkn]
  have hno := hp.no
  obtain eO : (out s₀ + BitVec.ofNat 32 (k * F.H.D)).setWidth 64 = (out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D) :=
    Pbkdf2.Stream.X86.setWidth_add (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega_using [hno, hkn, hn])
  obtain tO' : (out s₀ + BitVec.ofNat 32 (k * F.H.D)).toNat = (out s₀).toNat + k * F.H.D :=
    Pbkdf2.Stream.X86.toNat_add_ofNat (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega_arith)
  obtain osub : Region.Sub ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  unfold Fns.outLoop
  refine WP.seq (wp_mov fun s₁ u₁ => wp_arg hp (h.kr.upd (by decide) u₁) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ =>
    wp_movi fun s₄ u₄ => WP.block_nil ?_)
  obtain k₄ := (((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  obtain e₄si : s₄.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hcx]
  obtain e₄di : s₄.gpr .edi = out s₀ + BitVec.ofNat 32 (k * F.H.D) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, hdn]
  obtain e₄bx : s₄.gpr .ebx = s.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copyR_ok (so := F.tO) hn (by omega_using [hD, hnD]) e₄si u₄.gpr
    (by rw [k₄.ebp]; have hp_nsc := hp.nsc; omega_using [hp_nsc, he, hl, hnD]) (by rw [e₄di, tO']; omega_using [hno, hkn])
    (fun j hj => by
      rw [k₄.ebp]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [k₄.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_arith) (by omega_using [hj, hL, he, hl, hnD])⟩)
    (fun j hj => by
      rw [e₄di, eO]
      exact ⟨outR s₀, by rw [k₄.wr, hp.wr]; simp, by
        rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega_using [hj, hkn]) (by omega_using [hj, hol, hkn])⟩)
    (by rw [k₄.ebp, e₄di, eO]
        exact (hp.o_s.sub_left osub).symm.sub_left (part_sub (F := F) (by omega_using [he, hl, hnD])))) fun t c => ?_
  rw [k₄.ebp, e₄di, eO] at c
  obtain cm : t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
      (bytesAt s.mem (A s₀ F.tO) n) := by rw [c.mem, m₄]
  obtain f : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₄.mem t.mem := by
    rw [cm, m₄]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k₄.keep c.rd c.wr (fun r hr => c.other r (by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide))
    (rs := [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩]) f
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.o_s.sub_left osub).symm.sub_left (sv_sub hz))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩),
    by rw [c.other _ (by decide), e₄bx], by rw [c.other _ (by decide), e₄si], cm⟩

/-- The rest of a step: as much of `T` as the output needs, copied out,
`INT (k + 2)`, and whether that was the last block. -/
theorem tail_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s fun t =>
      Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nbk F s₀)) := by
  obtain hl := layout (F := F); have he := end_le hz; have hz_S := hz.S; have hD := hz.D
  obtain hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  have hno := hp.no
  obtain hkD : k * F.H.D < ol s₀ := (Whole.lt_nb hD.1).1 hk
  obtain hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega_arith
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  obtain hn : 0 < n := by omega_using [en, hkD, hD]
  obtain hkn : k * F.H.D + n ≤ ol s₀ := by omega_using [en, hkD]
  obtain hnD : n ≤ F.H.D := by omega_using [en]
  obtain hdn' : dn F s₀ (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega_using [en, hkD]
  obtain osub : Region.Sub ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hz hkD h) fun s₁ ⟨i₁, c₁, m₁⟩ => ?_)
  rw [en] at c₁
  refine WP.seq (WP.mono (outLoop_ok hp hz hn hkn hnD i₁ c₁ hkD) fun s₂ ⟨k₂, b₂, e₂, m₂⟩ => ?_)
  unfold Fns.advance
  refine wp_add fun s₃ u₃ => ?_
  obtain k₃ := k₂.upd (by decide) u₃
  refine wp_movm (a := A s₀ F.intO) (ea_scr hp k₃ (hz.intO_lt)) (by
      obtain ⟨r, hr, c⟩ := in_sc hp hz k₃.wr (o := F.intO) (n := 4) (end_le hz)
      exact ⟨r, List.mem_append_right _ hr, c⟩)
    fun s₄ u₄ => wp_bswap fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_bswap fun s₇ u₇ => ?_
  obtain k₇ := (((k₃.upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine wp_store (a := A s₀ F.intO) (ea_scr hp k₇ (hz.intO_lt)) (in_sc hp hz k₇.wr (end_le hz)) fun s₈ m₈ => ?_
  obtain fr₈ : Frame [sR s₀ F.intO 4] s₇.mem s₈.mem := by
    rw [m₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain k₈ := k₇.write hz m₈.rd m₈.wr (fun r _ => by rw [m₈.gpr]) (by omega_arith) (end_le hz) fr₈
  refine wp_arg hp k₈ (by decide) fun s₉ u₉ => wp_cmp fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  obtain m₁₀ : s₁₀.mem = s₂.mem.writeW (A s₀ F.intO) (s₇.gpr .eax) := by
    rw [f₁₀.mem, u₉.mem, m₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain fr₂ : Frame [sR s₀ F.intO 4] s₂.mem s₁₀.mem := by
    rw [m₁₀]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fr₁ : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain dI : (sR s₀ F.intO 4).Disjoint ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (end_le hz))).symm
  obtain r₂ : s₂.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₁.intW]
    exact fr₁.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  obtain e₇ : s₇.gpr .eax = byteRev32 (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, r₂, bswap_eq, bswap_eq, Whole.byteRev32_byteRev32, ofNat_succ32]
  obtain e₉ : s₉.gpr .ebx = BitVec.ofNat 32 (k * F.H.D + n) := by
    rw [u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, b₂, e₂, i₁.ebx, hdn, ← BitVec.ofNat_add]
  obtain hg : (Gk hF s₀ (k + 1)) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  obtain tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  refine ⟨⟨(k₈.upd (by decide) u₉).same f₁₀.rd f₁₀.wr (fun r _ => by rw [f₁₀.gpr]) f₁₀.mem, ?_, i₁.k0l,
    by rw [f₁₀.gpr, e₉, hdn'], by rw [m₁₀, Mem.readW_writeW_self32, e₇], ?_, ?_⟩, ?_⟩
  · refine i₁.st.keep hz (rs := [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩, sR s₀ F.intO 4])
      ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.o_s.sub_left osub).sub_right (part_sub (hz.st0O_3S))).symm
    · exact part_disj hz (Or.inl (by omega_using [hl])) (hz.st0O_3S) (end_le hz)
  · rw [hg, List.length_append, i₁.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨(out s₀).setWidth 64, k * F.H.D + n⟩ (outR s₀) := Region.sub_prefix hkn
    rw [hdn', bytes_keep fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (end_le hz))) (by omega_using [en, hkD, hol]), m₂]
    obtain bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₁.mem ((out s₀).setWidth 64) (k * F.H.D) (bytesAt s₁.mem (A s₀ F.tO) n)
      (by rw [bytesAt_length]; omega_using [en, hkD, hol])
    rw [bytesAt_length] at bw
    have ob := i₁.outB
    rw [hdn] at ob
    rw [bw, ob, Hmac.Generic.Common.bytesAt_take _ _ hnD, m₁, ht, hg, List.take_append,
      i₁.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₁.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₁.glen]; omega_using [])]
  · rw [z₁₀, e₉, u₉.gpr, arg_ofNat 6, sub_beq (by omega_using [en, hkD, hol]) (by omega_arith)]
    obtain e1 : k + 1 < nbk F s₀ ↔ (k + 1) * F.H.D < ol s₀ := Whole.lt_nb hD.1
    rw [Nat.succ_mul] at e1
    have : (arg s₀ 6).toNat = ol s₀ := rfl
    refine congrArg some (decide_eq_decide.2 ⟨fun h1 => ?_, fun h1 => ?_⟩)
    · by_contra h2
      have := e1.1 (by omega_using [h2, hk])
      omega_arith
    · have : ¬ (k * F.H.D + F.H.D < ol s₀) := fun h' => absurd (e1.2 h') (by omega_arith)
      omega_arith

/-! ## The loop and `pbkdf2` -/

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s fun t => Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nbk F s₀)) := by
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp hz h) fun s₁ ⟨i₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp hz i₁) fun s₂ ⟨i₂, di, si, ax, cx, dx, m₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp hz i₂ di si ax cx dx (by rw [m₂]; exact r₁)) fun s₃ ⟨i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp hz i₃) fun s₄ ⟨i₄, dx, si, ax, cx, di, m₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp hz i₄ dx si ax cx di (by rw [m₄]; exact r₃)) fun s₅ ⟨i₅, u₅⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp hz i₅ u₅) fun s₆ ⟨i₆, u₆, t₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp hz i₆) fun s₇ ⟨i₇, si, ax, cx, dx, m₇⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp hz i₇ si ax cx dx (by rw [m₇]; exact u₆) (by rw [m₇]; exact t₆))
    fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hz hk i₈ t₈

/-- The loop over the blocks of the output, if there are any. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) (hz' : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop F.block .ne)) s (Inv hF s₀ (nbk F s₀)) := by
  have hD := hz.D
  obtain e0 : nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  refine WP.ite (decide (ol s₀ = 0)) (by show eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz'])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [e0.2 (of_decide_eq_true h0)]; exact h
  · have hpos : 0 < nbk F s₀ := by
      have := of_decide_eq_false h0; have : nbk F s₀ ≠ 0 := fun e => this (e0.1 e); omega_arith
    exact count_loop hpos (Inv hF s₀) (fun k hk t ht => block_ok hp hz hk ht) h

theorem correct : WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hF.hH.SH (F.W + F.H.S)).post s₀ s' := by
  have hD := hz.D
  unfold Fns.pbkdf2
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (keyed_ok (hF := hF) hp hz k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hF h₂) fun s₃ ⟨k₃, st₃, kl₃⟩ => ?_)
  refine WP.seq (WP.mono (loopInit_ok hp hz k₃ st₃ kl₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz i₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  obtain hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (Pbkdf2.Stream.X86.restore_ok F.L k₅.ebp k₅.saved (by rw [k₅.wr]; exact sc_mem hp)
    (show 8 * F.W + 16 ≤ F.L8 by have hz_fits := hz.fits; omega_arith) hp.nsc)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k₅.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₅.esp]
    · exact hg r (Pbkdf2.Stream.X86.callee_saved r hr he)
  · have ob := h₅.outB
    obtain e : dn F s₀ (nbk F s₀) = ol s₀ := Whole.done_nb hD.1
    rw [e] at ob
    show Spec.Pbkdf2.pbkdf2Hmac _ _ _ _ _ = some (bytesAt s'.mem _ _)
    unfold Spec.Pbkdf2.pbkdf2Hmac
    rw [hF.hH.hD]
    exact Whole.pbkdf2_eq (prf hF s₀) (saltB s₀) hp.olD (by rw [hm, ob])

end

end VG.Proof.Pbkdf2.Whole.X86
