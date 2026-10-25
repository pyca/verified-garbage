module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the layout

What the proofs need of the functions `pbkdf2` calls (`FnsOK`): the facts
about the streaming functions (`HashOK`, from which HMAC's `init` and
`finalize` are correct), the constant time of HMAC's `init` and `finalize`,
and `iterate`, correct and constant time against `iterK` with `itW` bytes of
working space, with no frames. The proofs start from the state the inner
frame's body starts in (`s₀`, with the stack pointer at the inner frame
`fr`, `iterate`'s working space right above it and `X` bytes of stack below
it for the functions we call), whose precondition is `Pre`. The parts of
the inner frame (`sR`) are within it and apart from each other (`part_sub`,
`part_disj`); `KR` is what holds from the start of the frame's body on: the
regions, the stack pointer, the registers holding the arguments, our
caller's registers in the save area, and memory outside the frames, `out`
and the stack below the frames (`wrs`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open VG.Proof.Pbkdf2.RISCV64 (iterK)
open Spec.Sha256 (bytesAt)

/-- HMAC's `init`, with its frame and its callees' stack. -/
abbrev hiK (H : Hash) (SH : Spec.Hmac.StreamingHash) : Contract isa := initG SH (H.ibytes + H.F)

/-- HMAC's `finalize`, with its frame and its callees' stack. -/
abbrev hfK (H : Hash) (SH : Spec.Hmac.StreamingHash) : Contract isa := finG SH (H.fbytes + H.F)

/-- The facts about the functions `pbkdf2` calls. -/
structure FnsOK (F : Fns) where
  hH : HashOK F.H
  hiCt : ConstantTime isa (hiK F.H hH.SH).pre (hiK F.H hH.SH).pub F.H.init
  hfCt : ConstantTime isa (hfK F.H hH.SH).pre (hfK F.H hH.SH).pub F.H.finalize
  /-- `iterate`, correct and constant time with `itW` bytes of working space,
  pushing no frames. -/
  itOk : ∀ s, (iterK hH.SH F.itW).pre s →
    ∃ t s', Exec isa F.itC s t s' ∧ abiPreserved s s' ∧ (iterK hH.SH F.itW).post s s'
  itCt : ConstantTime isa (iterK hH.SH F.itW).pre (iterK hH.SH F.itW).pub F.itC
  itNf : F.itC.noFrames = true
  itW0 : 0 < F.itW
  /-- The frames are within what `alloc` reaches. -/
  itB : F.itB < 2048
  frB : F.frB < 2048

/-! ## The arguments and the regions -/

section
variable (F : Fns) (s₀ : State)

abbrev pw : Addr := s₀.gpr .a0
abbrev pwl : Nat := (s₀.gpr .a1).toNat
abbrev salt : Addr := s₀.gpr .a2
abbrev sl : Nat := (s₀.gpr .a3).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .a4).setWidth 32).toNat
abbrev out : Addr := s₀.gpr .a5
abbrev ol : Nat := (s₀.gpr .a6).toNat
abbrev pwR : Region := ⟨pw s₀, pwl s₀⟩
abbrev saltR : Region := ⟨salt s₀, sl s₀⟩
abbrev outR : Region := ⟨out s₀, ol s₀⟩
/-- An address in the inner frame, and a part of it. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨sA s₀ o, n⟩
/-- The inner frame, and `iterate`'s working space above it. -/
abbrev frR : Region := ⟨s₀.sp, F.frB⟩
abbrev itR : Region := sR s₀ F.frB F.itB
/-- The stack below the frames the functions we call use. -/
abbrev stk : Region := below s₀.sp F.X
/-- The save area. -/
abbrev svR : Region := sR s₀ 0 64
/-- Everything the code writes. -/
abbrev wrs : List Region := [frR F s₀, itR F s₀, outR s₀, stk F s₀]

end

/-- The state the inner frame's body starts in. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀]
  wr : s₀.wr = [frR F s₀, itR F s₀, outR s₀]
  pw_o : (pwR s₀).Disjoint (outR s₀)
  sa_o : (saltR s₀).Disjoint (outR s₀)
  f_pw : (frR F s₀).Disjoint (pwR s₀)
  f_sa : (frR F s₀).Disjoint (saltR s₀)
  f_o : (frR F s₀).Disjoint (outR s₀)
  i_pw : (itR F s₀).Disjoint (pwR s₀)
  i_sa : (itR F s₀).Disjoint (saltR s₀)
  i_o : (itR F s₀).Disjoint (outR s₀)
  al : s₀.sp.toNat % 16 = 0
  spX : F.X ≤ s₀.sp.toNat
  top : s₀.sp.toNat + F.frB + F.itB ≤ 2 ^ 64
  b_pw : (stk F s₀).Disjoint (pwR s₀)
  b_sa : (stk F s₀).Disjoint (saltR s₀)
  b_o : (stk F s₀).Disjoint (outR s₀)
  npw : (pw s₀).toNat + pwl s₀ ≤ 2 ^ 64
  nsa : (salt s₀).toNat + sl s₀ ≤ 2 ^ 64
  no : (out s₀).toNat + ol s₀ ≤ 2 ^ 64
  c0 : 0 < cc s₀
  olD : ol s₀ ≤ (2 ^ 32 - 1) * F.H.D

/-! ## The layout of the inner frame -/

section
variable {F : Fns}

/-- Where the parts of the inner frame are. -/
theorem layout : Fns.st0O = 64 ∧ F.st1O = 64 + F.H.S ∧ F.stWO = 64 + 2 * F.H.S ∧ F.uO = 64 + 3 * F.H.S ∧
    F.tO = 64 + 3 * F.H.S + F.H.D ∧ F.intO = 64 + 3 * F.H.S + 2 * F.H.D ∧
    F.bytes = 64 + 3 * F.H.S + 2 * F.H.D + 4 ∧ F.bytes ≤ F.frB ∧ F.frB % 16 = 0 ∧ F.itW ≤ F.itB ∧
    F.itB % 16 = 0 := by
  dsimp only [Fns.st0O, Fns.st1O, Fns.stWO, Fns.uO, Fns.tO, Fns.intO, Fns.bytes, Fns.frB, Fns.itB]
  omega

variable (hF : FnsOK F)
include hF

/-- The sizes the proofs use. -/
structure Sz (F : Fns) : Prop where
  N : 0 < F.H.N ∧ F.H.N ≤ 64
  B : F.H.B = 64 ∨ F.H.B = 128
  S : F.H.S = F.H.N + F.H.B
  D : 0 < F.H.D ∧ F.H.D ≤ 64 ∧ F.H.D ≤ F.H.B
  HF : F.H.F ≤ 1024
  X : F.H.ibytes + F.H.F ≤ F.X ∧ F.H.fbytes + F.H.F ≤ F.X ∧ F.H.F ≤ F.X ∧ F.X ≤ 4096
  frB : F.frB < 2048
  itB : F.itB < 2048

theorem sizes : Sz F := by
  have hl := hF.hH.lay
  have hB := hl.B
  have hD := hl.D
  have hS : F.H.S = F.H.N + F.H.B := rfl
  refine ⟨hl.N, hB, hS, ⟨hD.1, hD.2, by rcases hB with h | h <;> omega⟩, hl.F, ?_, hF.frB, hF.itB⟩
  have := hl.ibytes; have := hl.fbytes; have := hl.F
  simp only [Fns.X]
  omega

end

section
variable {F : Fns} {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ F.frB) : Region.Sub (sR s₀ o n) (frR F s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 4096) (hb : b + n ≤ 4096) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) :=
  Offset.disjoint _ h (by omega) (by omega)

omit hp in
theorem part_contains {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) : (frR F s₀).Contains (sA s₀ o) n :=
  Offset.contains_base _ h (by omega)

theorem fr_wr {s : State} (hwr : s.wr = s₀.wr) : frR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem it_wr {s : State} (hwr : s.wr = s₀.wr) : itR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem out_wr {s : State} (hwr : s.wr = s₀.wr) : outR s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem in_fr {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) :
    InRegions s.wr (sA s₀ o) n :=
  ⟨_, fr_wr hp hwr, part_contains (s₀ := s₀) h hr⟩

theorem in_fr' {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (fr_wr hp hwr), part_contains (s₀ := s₀) h hr⟩

/-- A part of the inner frame is covered by its regions. -/
theorem cov_part {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.frB) :
    RISCV64.Covers [sR s₀ o n] s.wr :=
  VG.Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, fr_wr hp hwr, o, rfl, h⟩

/-- The two frames are apart from each other and from the stack below them. -/
theorem f_i : (frR F s₀).Disjoint (itR F s₀) := by
  have := hp.top
  have := Offset.base_disjoint s₀.sp (k := F.frB) (e := F.frB) (n := F.itB) (Nat.le_refl _) (by omega)
  exact this

theorem f_s : (frR F s₀).Disjoint (stk F s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spX; have := s₀.sp.isLt; omega)

theorem i_s : (itR F s₀).Disjoint (stk F s₀) :=
  Offset.disjoint_below _ (by have := hp.top; have := hp.spX; have := s₀.sp.isLt; omega)

/-- The stack below the stack pointer, within `stk`. -/
theorem below_stk {n : Nat} (hn : n ≤ F.X) : Region.Sub (below s₀.sp n) (stk F s₀) :=
  below_sub hn (by have := hp.spX; have := s₀.sp.isLt; omega)

end

/-! ## What every piece keeps -/

/-- The callee-saved registers the code never writes. -/
abbrev nvRegs : List Reg := [.s0, .s8, .s9, .s10, .s11]

/-- The registers and memory kept from the start of the frame's body on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s1 : s.gpr .s1 = s₀.sp
  s2 : s.gpr .s2 = s₀.gpr .a3
  s3 : s.gpr .s3 = s₀.gpr .a4
  s6 : s.gpr .s6 = salt s₀
  nv : ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r
  saved : Spill.Saved s₀.sp s₀.gpr Fns.saved s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.s1, .s2, .s3, .s6, .s0, .s8, .s9, .s10, .s11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

theorem saved_fits : Spill.Fits Fns.saved := by
  refine ⟨fun q hq => ?_, by decide⟩
  simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saved_in : ∀ q ∈ Fns.saved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 64 := by
  intro q hq
  simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section
variable {F : Fns} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, Region.Disjoint (sR s₀ 0 64) r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') : KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.s1, (hg _ (by simp)).trans h.s2,
    (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s6,
    fun r hr => (hg r (by revert r; decide)).trans (h.nv r hr),
    h.saved.frame_in saved_in hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

open VG.RISCV64.Steps (Upd) in
theorem KR.upd {s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A part of the inner frame after the save area, `iterate`'s working
space, or the stack below the frames. -/
def Wk (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 64 ≤ o ∧ o + n ≤ F.frB) ∨ Region.Sub r (itR F s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ F.X

theorem Wk.ok (hp : Pre F s₀) (hz : Sz F) {r : Region} (h : Wk F s₀ r) :
    Region.Disjoint (sR s₀ 0 64) r ∧ ∃ r' ∈ wrs F s₀, Region.Sub r r' := by
  have hl := layout (F := F)
  have := hz.frB; have := hz.itB
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) (.inl h₁) (by omega) (by omega), _, by simp, part_sub (s₀ := s₀) h₂⟩
  · exact ⟨((f_i hp).sub_left (part_sub (s₀ := s₀) (o := 0) (n := 64) (by omega))).sub_right h,
      _, by simp, h⟩
  · exact ⟨((f_s hp).sub_left (part_sub (s₀ := s₀) (o := 0) (n := 64) (by omega))).sub_right
      (below_stk hp hn), _, by simp, below_stk hp hn⟩

/-- What a call leaves, writing parts of the frames after the save area and
the stack below them. -/
theorem KR.call (hp : Pre F s₀) (hz : Sz F) {s s' : State} (h : KR F s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    {rs : List Region} (hf : Frame rs s.mem s'.mem) (hw : ∀ r ∈ rs, Wk F s₀ r) : KR F s₀ s' :=
  h.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr)) hf (fun r hr => (Wk.ok hp hz (hw r hr)).1)
    (fun r hr => (Wk.ok hp hz (hw r hr)).2)

/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F s₀ s) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem KR.pwBytes (hp : Pre F s₀) {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (pw s₀) (pwl s₀) = bytesAt s₀.mem (pw s₀) (pwl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.f_pw.symm
    · exact hp.i_pw.symm
    · exact hp.pw_o
    · exact hp.b_pw.symm) (by show (s₀.gpr .a1).toNat ≤ 2 ^ 64; have := (s₀.gpr .a1).isLt; omega)

theorem KR.saltBytes (hp : Pre F s₀) {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.f_sa.symm
    · exact hp.i_sa.symm
    · exact hp.sa_o
    · exact hp.b_sa.symm) (by show (s₀.gpr .a3).toNat ≤ 2 ^ 64; have := (s₀.gpr .a3).isLt; omega)

end

end VG.Proof.Pbkdf2.Whole.RISCV64
