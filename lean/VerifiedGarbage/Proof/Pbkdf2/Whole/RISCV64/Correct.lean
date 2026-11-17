module

public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Init
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Bytes

/-! ### `Pbkdf2.Whole.RISCV64.Loop`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Whole.RISCV64.Block`, which this module and modules that import it used -/

section

/-! ### `Pbkdf2.Whole.RISCV64.Setup`, which only this module used -/

section

/-! ### `Pbkdf2.Whole.RISCV64.Calls`, which only this module used -/

section

/-! ### `Pbkdf2.Whole.RISCV64.Common`, which only this module used -/

section

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
  omega_using []

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
  refine ⟨hl.N, hB, hS, ⟨hD.1, hD.2, by rcases hB with h | h <;> omega_using [hD, h]⟩, hl.F, ?_, hF.frB, hF.itB⟩
  have := hl.ibytes; have := hl.fbytes; have := hl.F
  simp only [Fns.X]
  omega_arith

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
  Offset.disjoint _ h (by omega_using [ha]) (by omega_using [hb])

omit hp in
theorem part_contains {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) : (frR F s₀).Contains (sA s₀ o) n :=
  Offset.contains_base _ h (by omega_using [h, hr])

theorem fr_wr {s : State} (hwr : s.wr = s₀.wr) : frR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem it_wr {s : State} (hwr : s.wr = s₀.wr) : itR F s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem out_wr {s : State} (hwr : s.wr = s₀.wr) : outR s₀ ∈ s.wr := by rw [hwr, hp.wr]; simp

theorem in_fr {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) :
    InRegions s.wr (sA s₀ o) n :=
  ⟨_, fr_wr hp hwr, part_contains (s₀ := s₀) h hr⟩

theorem in_fr' {s : State} (hwr : s.wr = s₀.wr) {o n : Nat} (h : o + n ≤ F.frB) (hr : F.frB ≤ 4096) :
    InRegions (s.rd ++ s.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (fr_wr hp hwr), part_contains (s₀ := s₀) h hr⟩

/-- The two frames are apart from each other and from the stack below them. -/
theorem f_i : (frR F s₀).Disjoint (itR F s₀) := by
  have := hp.top
  have := Offset.base_disjoint s₀.sp (k := F.frB) (e := F.frB) (n := F.itB) (Nat.le_refl _) (by omega_using [this])
  exact this

theorem f_s : (frR F s₀).Disjoint (stk F s₀) :=
  Offset.base_disjoint_below _ (by have := hp.top; have := hp.spX; have := s₀.sp.isLt; omega_arith)

/-- The stack below the stack pointer, within `stk`. -/
theorem below_stk {n : Nat} (hn : n ≤ F.X) : Region.Sub (below s₀.sp n) (stk F s₀) :=
  below_sub hn (by have := hp.spX; have := s₀.sp.isLt; omega_arith)

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
  obtain hl := layout (F := F)
  have := hz.frB; have := hz.itB
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨part_disj (s₀ := s₀) (.inl h₁) (by omega_using []) (by omega_arith), _, by simp, part_sub (s₀ := s₀) h₂⟩
  · exact ⟨((f_i hp).sub_left (part_sub (s₀ := s₀) (o := 0) (n := 64) (by omega_using [hl]))).sub_right h,
      _, by simp, h⟩
  · exact ⟨((f_s hp).sub_left (part_sub (s₀ := s₀) (o := 0) (n := 64) (by omega_using [hl]))).sub_right
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
    · exact hp.b_pw.symm) (by show (s₀.gpr .a1).toNat ≤ 2 ^ 64; have := (s₀.gpr .a1).isLt; omega_using [])

theorem KR.saltBytes (hp : Pre F s₀) {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (salt s₀) (sl s₀) = bytesAt s₀.mem (salt s₀) (sl s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.f_sa.symm
    · exact hp.i_sa.symm
    · exact hp.sa_o
    · exact hp.b_sa.symm) (by show (s₀.gpr .a3).toNat ≤ 2 ^ 64; have := (s₀.gpr .a3).isLt; omega_using [])

end

end VG.Proof.Pbkdf2.Whole.RISCV64

end

end


/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the calls

The calls of HMAC's `init` and `finalize` (against the contracts of their
generic proofs, `WP.callAny`, since they allocate their working space on the
stack), of `iterate` (against `iterK`, `WP.call`, since it pushes no frames)
and of the streaming `update` (`HashOK.callUpd_ok`): what each needs of the
state it is called from, and what holds when it returns; and, for the first
three, that two runs of the call with the same arguments leak the same
trace (`RelCT.call`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initG finG)
open VG.Proof.Pbkdf2.RISCV64 (iterK)
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

theorem hi_sdepth (hH : HashOK F.H) : sdepth F.H.init ≤ F.H.ibytes + F.H.F := by
  obtain h₁ := hH.initSd; have h₂ := hH.updSd; have h₃ := hH.finSd
  simp only [Hash.init, Hash.initMain, Hash.longKey, Hash.padKey, Hash.updBlock, Hash.callInit, Hash.callUpd,
    Hash.callFin, Hash.keyLoop, Hash.padLoop, sdepth, Instr.frameBytes]
  simp only [Nat.add_le_add_iff_left, Nat.max_le, Nat.zero_le, h₁, h₂, h₃, and_self]

theorem hf_sdepth (hH : HashOK F.H) : sdepth F.H.finalize ≤ F.H.fbytes + F.H.F := by
  have := hH.updSd; have := hH.finSd
  simp only [Hash.finalize, Hash.finalizeMain, Hash.callUpd, Hash.callFin, sdepth, Instr.frameBytes]
  omega_arith

theorem hi_ok : ∀ s, (hiK F.H hF.hH.SH).pre s → ∃ t s', Exec isa F.H.init s t s' ∧
    abiPreserved s s' ∧ (hiK F.H hF.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Init.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

theorem hf_ok : ∀ s, (hfK F.H hF.hH.SH).pre s → ∃ t s', Exec isa F.H.finalize s t s' ∧
    abiPreserved s s' ∧ (hfK F.H hF.hH.SH).post s s' := fun _ hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Hmac.Stream.RISCV64.Finalize.correct hF.hH hs
  exact ⟨t, s', he, h₁, h₂⟩

/-- What a call of HMAC's `init` needs of the state it is called from: the
key's `kl` bytes at `k` and the states at `inn` and `ou`. -/
structure HiArgs (F : Fns) (s : State) (inn ou k : Addr) (kl : Nat) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a2 : s.gpr .a2 = k
  a3 : (s.gpr .a3).toNat = kl
  al : s.sp.toNat % 16 = 0
  sp : F.H.ibytes + F.H.F ≤ s.sp.toNat
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_ki : Region.Disjoint ⟨k, kl⟩ ⟨inn, F.H.S⟩
  d_ko : Region.Disjoint ⟨k, kl⟩ ⟨ou, F.H.S⟩
  b_i : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨inn, F.H.S⟩
  b_o : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨ou, F.H.S⟩
  b_k : (below s.sp (F.H.ibytes + F.H.F)).Disjoint ⟨k, kl⟩
  hc : RISCV64.Covers ([⟨k, kl⟩] ++ [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] s.wr

include hF in
theorem HiArgs.pre {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs F s inn ou k kl) :
    (hiK F.H hF.hH.SH).pre (s.callEntry.withRegions [⟨k, kl⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) := by
  have hS := hF.hH.hS
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, hS]
  exact ⟨trivial, trivial, h.d_io, h.d_ki, h.d_ko, h.al, h.sp, h.b_i, h.b_o, h.b_k⟩

/-- HMAC's `init` with the key's `kl` bytes at `k`, into the states at `inn` and `ou`. -/
theorem hi_call {s : State} {inn ou k : Addr} {kl : Nat} (h : HiArgs F s inn ou k kl) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨ou, F.H.S⟩] ++ [below s.sp (F.H.ibytes + F.H.F)]) s' →
      hF.hH.SH.Repr s'.mem inn (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hF.hH.SH.Repr s'.mem ou (xorPad (blockKey hF.hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa F.callHi s Q := by
  have hS := hF.hH.hS
  have hl := hF.hH.lay
  obtain c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  obtain c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  obtain c2 : s.callEntry.gpr .a2 = k := (State.callEntry_gpr _ (by decide)).trans h.a2
  obtain c3 : (s.callEntry.gpr .a3).toNat = kl := by rw [State.callEntry_gpr _ (by decide), h.a3]
  refine WP.callAny (k := hiK F.H hF.hH.SH) (hi_ok hF) (rd := [⟨k, kl⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]) (h.pre hF) (by rw [hS]; exact h.hc)
    (by rw [hS]; exact h.hw) ?_ (by have := hi_sdepth hF.hH; have := hl.ibytes; have := hl.F; omega_arith)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
    c3] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost.1 hpost.2
  rw [hS] at hf
  exact Frame.below_mono hf (hi_sdepth hF.hH) (by have := hl.ibytes; have := hl.F; omega_arith)

include hF in
/-- Two runs of a call of HMAC's `init` with the same arguments. -/
theorem hi_rel {P : State → State → Prop} {inn ou k : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs F s inn ou k kl ∧ HiArgs F s' inn ou k kl ∧ s.sp = s'.sp) :
    RelCT isa P F.callHi fun _ _ => True := by
  have hS := hF.hH.hS
  refine RelCT.call (hi_ok hF) hF.hiCt [⟨k, kl⟩] [⟨inn, hF.hH.SH.stateBytes⟩, ⟨ou, hF.hH.SH.stateBytes⟩]
    fun s s' hp => ?_
  obtain ⟨a, a', e⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS]; exact a.hc, by rw [hS]; exact a.hw, by rw [hS]; exact a'.hc,
    by rw [hS]; exact a'.hw⟩
  simp only [hiK, initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a2, a'.a2]
  simp only [true_and]
  exact ⟨BitVec.eq_of_toNat_eq (a.a3.trans a'.a3.symm), e⟩

/-! ## HMAC's `finalize` -/

/-- What a call of HMAC's `finalize` needs: the inner state at `inn`, the
outer state at `ou` and `out` at `o`. -/
structure HfArgs (F : Fns) (s : State) (inn ou o : Addr) : Prop where
  a0 : s.gpr .a0 = inn
  a1 : s.gpr .a1 = ou
  a3 : s.gpr .a3 = o
  al : s.sp.toNat % 16 = 0
  sp : F.H.fbytes + F.H.F ≤ s.sp.toNat
  d_iu : Region.Disjoint ⟨inn, F.H.S⟩ ⟨ou, F.H.S⟩
  d_io : Region.Disjoint ⟨inn, F.H.S⟩ ⟨o, F.H.D⟩
  d_uo : Region.Disjoint ⟨ou, F.H.S⟩ ⟨o, F.H.D⟩
  b_i : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨inn, F.H.S⟩
  b_u : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨ou, F.H.S⟩
  b_o : (below s.sp (F.H.fbytes + F.H.F)).Disjoint ⟨o, F.H.D⟩
  hc : RISCV64.Covers ([⟨ou, F.H.S⟩] ++ [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨inn, F.H.S⟩, ⟨o, F.H.D⟩] s.wr

include hF in
theorem HfArgs.pre {s : State} {inn ou o : Addr} (h : HfArgs F s inn ou o) :
    (hfK F.H hF.hH.SH).pre (s.callEntry.withRegions [⟨ou, hF.hH.SH.stateBytes⟩]
      [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩]) := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    h.a0, h.a1, h.a3, hS, hD]
  exact ⟨trivial, trivial, h.d_iu, h.d_io, h.d_uo, h.al, h.sp, h.b_i, h.b_u, h.b_o⟩

/-- HMAC's `finalize` of the inner state at `inn` and the outer state at
`ou`, with `count` in `a2`, into `o`. -/
theorem hf_call {s : State} {inn ou o : Addr} (h : HfArgs F s inn ou o) {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨inn, F.H.S⟩, ⟨o, F.H.D⟩] ++ [below s.sp (F.H.fbytes + F.H.F)]) s' →
      (∀ k0 text, k0.length = F.H.B → k0.length + text.length < 2 ^ 64 →
        hF.hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) →
        s.gpr .a2 = BitVec.ofNat 64 (F.H.B + text.length) →
        hF.hH.SH.Repr s.mem ou (xorPad k0 opad) →
        bytesAt s'.mem o F.H.D = hmacBlockKey hF.hH.SH.H k0 text) → Q s') :
    WP isa F.callHf s Q := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have hl := hF.hH.lay
  obtain c0 : s.callEntry.gpr .a0 = inn := (State.callEntry_gpr _ (by decide)).trans h.a0
  obtain c1 : s.callEntry.gpr .a1 = ou := (State.callEntry_gpr _ (by decide)).trans h.a1
  obtain c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  obtain c3 : s.callEntry.gpr .a3 = o := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.callAny (k := hfK F.H hF.hH.SH) (hf_ok hF) (rd := [⟨ou, hF.hH.SH.stateBytes⟩])
    (wr := [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩]) (h.pre hF) (by rw [hS, hD]; exact h.hc)
    (by rw [hS, hD]; exact h.hw) ?_ (by have := hf_sdepth hF.hH; have := hl.fbytes; have := hl.F; omega_arith)
  intro s' hrd hwr hsp' hf hcs hpost
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hS, hD] at hf
  exact Frame.below_mono hf (hf_sdepth hF.hH) (by have := hl.fbytes; have := hl.F; omega_arith)

include hF in
/-- Two runs of a call of HMAC's `finalize` with the same arguments. -/
theorem hf_rel {P : State → State → Prop} {inn ou o : Addr}
    (h : ∀ s s', P s s' → HfArgs F s inn ou o ∧ HfArgs F s' inn ou o ∧ s.sp = s'.sp ∧
      s.gpr .a2 = s'.gpr .a2) :
    RelCT isa P F.callHf fun _ _ => True := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call (hf_ok hF) hF.hfCt [⟨ou, hF.hH.SH.stateBytes⟩]
    [⟨inn, hF.hH.SH.stateBytes⟩, ⟨o, hF.hH.SH.digestBytes⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hS, hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hS, hD]; exact a'.hw⟩
  simp only [hfK, finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, e2]
  simp only [true_and]
  exact e

/-! ## `iterate` -/

/-- What a call of `iterate` needs: the key's states at `key`, `U` at `u`,
`T` at `t` and the working space at `sc`. -/
structure ItArgs (F : Fns) (s : State) (key u t sc : Addr) : Prop where
  a0 : s.gpr .a0 = key
  a1 : s.gpr .a1 = u
  a3 : s.gpr .a3 = t
  a4 : s.gpr .a4 = sc
  d_kt : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨t, F.H.D⟩
  d_ks : Region.Disjoint ⟨key, 2 * F.H.S⟩ ⟨sc, F.itW⟩
  d_ut : Region.Disjoint ⟨u, F.H.D⟩ ⟨t, F.H.D⟩
  d_us : Region.Disjoint ⟨u, F.H.D⟩ ⟨sc, F.itW⟩
  d_ts : Region.Disjoint ⟨t, F.H.D⟩ ⟨sc, F.itW⟩
  hc : RISCV64.Covers ([⟨key, 2 * F.H.S⟩, ⟨u, F.H.D⟩] ++ [⟨t, F.H.D⟩, ⟨sc, F.itW⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨t, F.H.D⟩, ⟨sc, F.itW⟩] s.wr

include hF in
theorem ItArgs.pre {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) :
    (iterK hF.hH.SH F.itW).pre (s.callEntry.withRegions
      [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
      [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩]) := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs),
    h.a0, h.a1, h.a3, h.a4, hS, hD]
  exact ⟨trivial, trivial, h.d_kt, h.d_ks, h.d_ut, h.d_us, h.d_ts⟩

/-- `iterate` with the key's states at `key`, `U` at `u`, `n` in `a2`, `T` at
`t` and the working space at `sc`. -/
theorem it_call {s : State} {key u t sc : Addr} (h : ItArgs F s key u t sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨t, F.H.D⟩, ⟨sc, F.itW⟩] s' →
      (∀ k0, k0.length = F.H.B → hF.hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hF.hH.SH.Repr s.mem (key + BitVec.ofNat 64 F.H.S) (xorPad k0 opad) →
        bytesAt s'.mem t F.H.D = Spec.Pbkdf2.iterate (hmacBlockKey hF.hH.SH.H k0)
          ((s.gpr .a2).setWidth 32).toNat (bytesAt s.mem u F.H.D) (bytesAt s.mem t F.H.D)) → Q s') :
    WP isa F.callIt s Q := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  obtain c0 : s.callEntry.gpr .a0 = key := (State.callEntry_gpr _ (by decide)).trans h.a0
  obtain c1 : s.callEntry.gpr .a1 = u := (State.callEntry_gpr _ (by decide)).trans h.a1
  obtain c2 : s.callEntry.gpr .a2 = s.gpr .a2 := State.callEntry_gpr _ (by decide)
  obtain c3 : s.callEntry.gpr .a3 = t := (State.callEntry_gpr _ (by decide)).trans h.a3
  refine WP.call (k := iterK hF.hH.SH F.itW) hF.itOk (h.pre hF)
    (by rw [hS, hD]; exact h.hc) (by rw [hD]; exact h.hw) ?_ hF.itNf
  intro s' hrd hwr hsp' hf hcs _ hpost
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3,
    hD, hB, hS] at hpost
  refine hQ s' ⟨hrd, hwr, hsp', hcs, ?_⟩ hpost
  rw [hD] at hf
  exact hf

include hF in
/-- Two runs of a call of `iterate` with the same arguments. -/
theorem it_rel {P : State → State → Prop} {key u t sc : Addr}
    (h : ∀ s s', P s s' → ItArgs F s key u t sc ∧ ItArgs F s' key u t sc ∧ s.sp = s'.sp ∧
      (s.gpr .a2).setWidth 32 = (s'.gpr .a2).setWidth 32) :
    RelCT isa P F.callIt fun _ _ => True := by
  obtain hS := hF.hH.hS; have hD := hF.hH.hD
  refine RelCT.call hF.itOk hF.itCt [⟨key, 2 * hF.hH.SH.stateBytes⟩, ⟨u, hF.hH.SH.digestBytes⟩]
    [⟨t, hF.hH.SH.digestBytes⟩, ⟨sc, F.itW⟩] fun s s' hp => ?_
  obtain ⟨a, a', e, e2⟩ := h s s' hp
  refine ⟨a.pre hF, a'.pre hF, ?_, by rw [hS, hD]; exact a.hc, by rw [hD]; exact a.hw,
    by rw [hS, hD]; exact a'.hc, by rw [hD]; exact a'.hw⟩
  simp only [iterK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a2 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), State.callEntry_gpr s' (by decide : Reg.a4 ∉ linkRegs),
    a.a0, a'.a0, a.a1, a'.a1, a.a3, a'.a3, a.a4, a'.a4, e2]
  simp only [true_and]
  exact e

/-! ## The streaming `update` -/

/-- What a call of the streaming `update` needs: the state at `st` and the
`len` bytes at `dat`. -/
structure UpdArgs (F : Fns) (s : State) (st dat : Addr) (len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a2 : s.gpr .a2 = dat
  a3 : (s.gpr .a3).toNat = len
  d : Region.Disjoint ⟨dat, len⟩ ⟨st, F.H.S⟩
  al : s.sp.toNat % 16 = 0
  sp : F.H.F ≤ s.sp.toNat
  b_s : (below s.sp F.H.F).Disjoint ⟨st, F.H.S⟩
  b_d : (below s.sp F.H.F).Disjoint ⟨dat, len⟩
  hc : RISCV64.Covers ([⟨dat, len⟩] ++ [⟨st, F.H.S⟩]) (s.rd ++ s.wr)
  hw : RISCV64.Covers [⟨st, F.H.S⟩] s.wr

/-- The streaming `update`, as `HashOK.callUpd_ok` gives it. -/
theorem upd_call (hH : HashOK F.H) {s : State} {st dat : Addr} {len : Nat} (h : UpdArgs F s st dat len)
    {Q : State → Prop}
    (hQ : ∀ s', After s ([⟨st, F.H.S⟩] ++ [below s.sp F.H.F]) s' →
      (∀ m, hH.SH.Repr s.mem st m → s.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem st (m ++ bytesAt s.mem dat len)) → Q s') :
    WP isa F.H.callUpd s Q :=
  hH.callUpd_ok h.a0 h.a2 h.a3 h.d h.al h.sp h.b_s h.b_d h.hc h.hw
    fun s' a b c d e f => hQ s' ⟨a, b, c, e, d⟩ f

end VG.Proof.Pbkdf2.Whole.RISCV64

end

end


/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the setup

From the start of the inner frame's body, the prologue saves our caller's
`ra` and `s1`–`s7` at the start of the frame and moves the arguments into
`s1`–`s6` (`prologue_ok`); HMAC's `init` makes the key's inner and outer
states (`States`, of `K₀`, the password made a key, `K0`; `hi_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_addSp)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open Spec.Hmac (xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- After the prologue: `KR`, the output in `s4` and `s5`, and HMAC's
`init`'s arguments. -/
structure Pro (F : Fns) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  s4 : s.gpr .s4 = out s₀
  s5 : s.gpr .s5 = s₀.gpr .a6
  a0 : s.gpr .a0 = sA s₀ Fns.st0O
  a1 : s.gpr .a1 = sA s₀ F.st1O
  a2 : s.gpr .a2 = pw s₀
  a3 : s.gpr .a3 = s₀.gpr .a1

theorem prologue_eq : F.prologue = .addSp .t0 0 :: (Spill.saveCode .t0 Fns.saved ++
    [mov .s1 .t0, mov .s2 .a3, mov .s3 .a4, mov .s4 .a5, mov .s5 .a6, mov .s6 .a2, mov .a2 .a0, mov .a3 .a1,
      .addi .a0 .s1 Fns.st0O, .addi .a1 .s1 F.st1O]) := rfl

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F s₀)
include hF hp

theorem prologue_ok : WP isa (.block F.prologue) s₀ (Pro F s₀) := by
  obtain hz := sizes hF
  obtain hl := layout (F := F)
  have hfr := hz.frB
  rw [prologue_eq]
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  obtain t0 : s₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  obtain e₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  refine Spill.save_ok (b := .t0) (by rw [t0]; omega_using [hp.al])
    (fun q hq => by
      simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_fr hp rfl (by have := saved_in q hq; omega_using [hl, this]) (by omega_using [hfr])) ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ =>
    wp_addi (by simp only [Fns.st0O]; omega_using []) fun s₁₀ u₁₀ => wp_addi (by omega_using [hl, hfr]) fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain mm : s₁₁.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr Fns.saved := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr Fns.saved = _
    rw [t0]
  obtain gg : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s5, .s6, .a2, .a3, .a0, .a1] → s₁₁.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g, h, i, j, k⟩ := hr
    exact (u₁₁.other r k).trans ((u₁₀.other r j).trans ((u₉.other r i).trans ((u₈.other r h).trans
      ((u₇.other r g).trans ((u₆.other r f).trans ((u₅.other r d).trans ((u₄.other r c).trans
      ((u₃.other r b).trans (u₂.other r a)))))))))
  obtain sv : Spill.Saved s₀.sp s₀.gpr Fns.saved s₁₁.mem := by
    rw [mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [Fns.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  obtain q1 : s₁₁.gpr .s1 = s₀.sp := by
    upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact t0
  have r : ∀ q, q ≠ .t0 → s₁.gpr q = s₀.gpr q := e₁
  refine ⟨⟨by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd,
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr,
    by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp,
    q1, ?_, ?_, ?_, fun q hq => ?_, sv, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · rw [gg q (by revert q; decide), r q (by revert q hq; decide)]
  · rw [mm, u₁.mem]
    refine ((Spill.saveMem_frame_base (n := 64) (fun p hp' => (saved_in p hp').2) (by omega_using []) _ _ _).sub
      fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR F s₀, by simp, Region.sub_prefix (by omega_using [hl])⟩
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [t0]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    rw [t0]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other,
      u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact r _ (by decide)

end

/-! ## HMAC's states for the key -/

/-- The key `K₀`: the password, or its digest, padded to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte := blockKey hF.hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- The key's inner and outer states. -/
def States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop :=
  hF.hH.SH.Repr m (sA s₀ Fns.st0O) (xorPad (K0 hF s₀) ipad) ∧
    hF.hH.SH.Repr m (sA s₀ F.st1O) (xorPad (K0 hF s₀) opad)

theorem sA_add (s₀ : State) (a b : Nat) : sA s₀ a + BitVec.ofNat 64 b = sA s₀ (a + b) := by
  show s₀.sp + BitVec.ofNat 64 a + BitVec.ofNat 64 b = s₀.sp + BitVec.ofNat 64 (a + b)
  rw [BitVec.ofNat_add, BitVec.add_assoc]

section
variable {hF : FnsOK F} {s₀ : State}

/-- The key's states survive writes apart from them. -/
theorem States.keep {m m' : Mem} (h : States hF s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ Fns.st0O (2 * F.H.S)) r) : States hF s₀ m' := by
  obtain hz := sizes hF
  obtain hS : F.H.S ≤ 256 := by have := hz.N; have := hz.B; rw [hz.S]; omega_arith
  refine ⟨hF.hH.congr m m' _ _ (fun i hi => ?_) h.1, hF.hH.congr m m' _ _ (fun i hi => ?_) h.2⟩
  · exact hf.bytes (R := sR s₀ Fns.st0O F.H.S) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_using [])))
      (by show F.H.S ≤ 2 ^ 64; omega_using [hS]) hi
  · have := hf.bytes (R := sR s₀ Fns.st0O (2 * F.H.S)) (hd · ·) (by show 2 * F.H.S ≤ 2 ^ 64; omega_using [hS])
      (i := F.H.S + i) (by show F.H.S + i < 2 * F.H.S; omega_using [hi])
    obtain e : sA s₀ Fns.st0O + BitVec.ofNat 64 (F.H.S + i) = sA s₀ F.st1O + BitVec.ofNat 64 i := by
      rw [sA_add, sA_add, show Fns.st0O + (F.H.S + i) = F.st1O + i by simp only [Fns.st1O]; omega_using []]
    rwa [e] at this

end

/-- After HMAC's `init`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  s4 : s.gpr .s4 = out s₀
  s5 : s.gpr .s5 = s₀.gpr .a6
  st : States hF s₀ s.mem

section
variable (hF : FnsOK F) {s₀ : State} (hp : Pre F s₀)
include hF hp

/-- HMAC's `init`'s arguments, after the prologue. -/
theorem hi_args {s : State} (h : Pro F s₀ s) :
    HiArgs F s (sA s₀ Fns.st0O) (sA s₀ F.st1O) (pw s₀) (pwl s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hX := hz.X; have hfr := hz.frB
  obtain bsub : Region.Sub (below s.sp (F.H.ibytes + F.H.F)) (stk F s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega_using [hX])
  obtain p0 : Region.Sub (sR s₀ Fns.st0O F.H.S) (frR F s₀) := part_sub (by omega_using [hl])
  obtain p1 : Region.Sub (sR s₀ F.st1O F.H.S) (frR F s₀) := part_sub (by omega_using [hl])
  refine ⟨h.a0, h.a1, h.a2, by rw [h.a3], by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega_using [hX, this],
    part_disj (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]), (hp.f_pw.sub_left p0).symm,
    (hp.f_pw.sub_left p1).symm, (f_s hp).sub_left p0 |>.symm.sub_left bsub,
    (f_s hp).sub_left p1 |>.symm.sub_left bsub, hp.b_pw.sub_left bsub, ?_, ?_⟩
  · rw [h.kr.rd, h.kr.wr, hp.rd, hp.wr]
    refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨pwR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨frR F s₀, by simp, Fns.st0O, rfl, by show Fns.st0O + F.H.S ≤ F.frB; omega_using [hl]⟩
    · exact ⟨frR F s₀, by simp, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.frB; omega_using [hl]⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨frR F s₀, fr_wr hp h.kr.wr, Fns.st0O, rfl, by show Fns.st0O + F.H.S ≤ F.frB; omega_using [hl]⟩
    · exact ⟨frR F s₀, fr_wr hp h.kr.wr, F.st1O, rfl, by show F.st1O + F.H.S ≤ F.frB; omega_using [hl]⟩

theorem hi_ok' {s : State} (h : Pro F s₀ s) : WP isa F.callHi s (Keyed hF s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hX := hz.X; have hfr := hz.frB
  refine hi_call hF (hi_args hF hp h) fun s' a hI hO => ?_
  obtain kr' := h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, by simp only [Fns.st0O]; omega_using [], by omega_using [hl]⟩
    · exact .inl ⟨_, _, rfl, by omega_using [hl], by omega_using [hl]⟩
    · exact .inr (.inr ⟨_, by rw [h.kr.sp], by omega_using [hX]⟩)
  rw [h.kr.pwBytes hp] at hI hO
  exact ⟨kr', by rw [a.cs _ (by decide), h.s4], by rw [a.cs _ (by decide), h.s5], hI, hO⟩

end

end VG.Proof.Pbkdf2.Whole.RISCV64

end

end


/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: a block, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `s4` points past them, `s5` counts the bytes left and
`s7` is `k + 1`. A block copies the key's inner state into the working
state (`HashOK.reloc`: it represents a whole block), absorbs the salt and
`INT (k + 1)` (written from `s7`) into it with `update`, and computes `U₁`
with HMAC's `finalize` (`b6_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_srl wp_sb)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Pbkdf2.RISCV64 (It)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem blockKey_length (hH : HashOK F.H) (k : List Byte) : (blockKey hH.SH.H k).length = F.H.B := by
  have hB := hH.hB
  obtain hDB : F.H.D ≤ F.H.B := by have := hH.hD64; rcases hH.hB64 with h | h <;> omega_using [this, h]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hH.hashLen]; omega_using [hDB]
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
  kr : KR F s₀ s
  st : States hF s₀ s.mem
  s4 : s.gpr .s4 = out s₀ + BitVec.ofNat 64 (dn s₀ (F := F) k)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (k + 1)
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (out s₀) (dn s₀ (F := F) k) = (Gk hF s₀ k).take (dn s₀ (F := F) k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := .s4 :: .s5 :: .s7 :: kregs

/-- Where a block writes, before it copies `T` out: the parts of the inner
frame from the working state on, `iterate`'s working space, and the stack
below the frames. -/
def Wb (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.frB) ∨ Region.Sub r (itR F s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ F.X

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem Wb.ok {r : Region} (h : Wb F s₀ r) :
    Wk F s₀ r ∧ (sR s₀ Fns.st0O (2 * F.H.S)).Disjoint r ∧ (outR s₀).Disjoint r := by
  obtain hz := sizes hF; have hl := layout (F := F); have := hz.frB; have := hz.itB
  obtain p0 : Region.Sub (sR s₀ Fns.st0O (2 * F.H.S)) (frR F s₀) := part_sub (by omega_using [hl])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨.inl ⟨o, n, rfl, by omega_using [hl, h₁], h₂⟩, part_disj (.inl (by omega_using [hl, h₁])) (by omega_arith) (by omega_arith),
      hp.f_o.symm.sub_right (part_sub h₂)⟩
  · exact ⟨.inr (.inl h), ((f_i hp).sub_left p0).sub_right h, hp.i_o.symm.sub_right h⟩
  · have hsub := below_stk hp hn
    exact ⟨.inr (.inr ⟨n, rfl, hn⟩), ((f_s hp).sub_left p0).sub_right hsub, (hp.b_o.symm).sub_right hsub⟩

/-- `Inv` survives writes where a block writes. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wb F s₀ r) : Inv hF s₀ k s' := by
  obtain hz := sizes hF
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))) hf
      (fun r hr => (Wk.ok hp hz (Wb.ok (hF := hF) hp (hw r hr)).1).1) (fun r hr => (Wk.ok hp hz (Wb.ok (hF := hF) hp (hw r hr)).1).2),
    h.st.keep hf (fun r hr => (Wb.ok (hF := hF) hp (hw r hr)).2.1), by rw [hg _ (by simp), h.s4],
    by rw [hg _ (by simp), h.s5], by rw [hg _ (by simp), h.s7], h.glen, ?_⟩
  rw [← h.outB]
  obtain osub : Region.Sub ⟨out s₀, dn s₀ (F := F) k⟩ (outR s₀) := Region.sub_prefix (Nat.min_le_right _ _)
  exact Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨out s₀, dn s₀ (F := F) k⟩)
    (fun r hr => ((Wb.ok (hF := hF) hp (hw r hr)).2.2).sub_left osub)
    (by have e1 : dn s₀ (F := F) k ≤ ol s₀ := Nat.min_le_right _ _
        obtain e2 : ol s₀ < 2 ^ 64 := (s₀.gpr .a6).isLt
        show dn s₀ (F := F) k ≤ 2 ^ 64; omega_using [e1, e2]) hi

/-- `n` bytes copied from offset `a` of the inner frame to offset `b`, where a
block writes. -/
theorem copy_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {a b n : Nat} (hab : a + n ≤ b ∨ b + n ≤ a)
    (ha : a + n ≤ F.frB) (hbo : F.stWO ≤ b) (hb : b + n ≤ F.frB) {rest : List Instr} {Q : State → Prop}
    (hk : ∀ t, Inv hF s₀ k t → (∀ r, r ≠ .t1 → t.gpr r = s.gpr r) →
      t.mem = writeBytes s.mem (sA s₀ b) (bytesAt s.mem (sA s₀ a) n) → WP isa (.block rest) t Q) :
    WP isa (.block (It.cp .s1 .s1 a b n ++ rest)) s Q := by
  obtain hz := sizes hF; have hfr := hz.frB
  obtain e : ∀ o j, s.gpr .s1 + BitVec.ofNat 64 o + BitVec.ofNat 64 j = sA s₀ (o + j) := fun o j => by
    rw [h.kr.s1, sA_add]
  refine VG.Proof.Pbkdf2.RISCV64.cp_ok (src := .s1) (dst := .s1) (by decide) (by decide) a b n (by omega_using [ha, hfr])
    (by omega_using [hb, hfr]) rest s Q
    (fun j hj => by rw [e]; exact in_fr' hp h.kr.wr (by omega_using [ha, hj]) (by omega_using [hfr]))
    (fun j hj => by rw [e]; exact in_fr hp h.kr.wr (by omega_using [hb, hj]) (by omega_using [hfr]))
    (by rw [h.kr.s1]; exact Offset.sep _ hab (by have := hp.top; omega_using [ha, hfr]) (by have := hp.top; omega_using [hb, hfr]))
    fun t g rd wr sp m => ?_
  rw [h.kr.s1] at m
  refine hk t (h.keep hp rd wr sp (fun r hr => g r (by revert r; decide)) (rs := [sR s₀ b n]) ?_
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨b, n, rfl, hbo, hb⟩)) g m
  rw [m]
  exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

/-- The key's inner state copied into the working state, which then
represents `K₀ ⊕ ipad`, and `update`'s arguments for the salt. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.saltArgs) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad) ∧ t.gpr .a0 = sA s₀ F.stWO ∧
      t.gpr .a1 = BitVec.ofNat 64 F.H.B ∧ t.gpr .a2 = salt s₀ ∧ t.gpr .a3 = s₀.gpr .a3 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  unfold Fns.saltArgs
  refine copy_ok hp h (a := Fns.st0O) (b := F.stWO) (n := F.H.S) (by omega_using [hl]) (by omega_using [hl]) (Nat.le_refl _)
    (by omega_using [hl]) fun t ht g m => ?_
  refine wp_addi (by omega_using [hl, hfr]) fun s₁ u₁ => wp_li (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  obtain mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨ht.keep hp (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₄.other r (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide),
        u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm]
    obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    refine hF.hH.reloc s.mem t.mem _ _ _ (by rw [xorPad_length, hK]; exact Nat.mod_self _) (fun i hi => ?_) h.st.1
    have := hz.S
    rw [m, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [bytesAt_length]; omega_using [hi, this])
      (by rw [bytesAt_length]; omega_using [hl, hfr]), VG.Proof.Hmac.Common.bytesAt_getD' _ _ (by omega_using [hi, this])]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s6]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s2]

/-- The salt and the inner frame fit in the address space together. -/
theorem sl_bytes : sl s₀ + F.frB ≤ 2 ^ 64 :=
  Whole.len_add_le hp.f_sa.symm hp.nsa (by have := hp.top; show s₀.sp.toNat + F.frB ≤ 2 ^ 64; omega_using [this])

/-- `update`'s arguments for the working state, with the `len` bytes at `dat`. -/
theorem updW_args {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat}
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h2 : s.gpr .a2 = dat) (h3 : (s.gpr .a3).toNat = len)
    (hd : Region.Disjoint ⟨dat, len⟩ (sR s₀ F.stWO F.H.S)) (hs : (stk F s₀).Disjoint ⟨dat, len⟩)
    (hcd : ∃ r' ∈ s.rd ++ s.wr, ∃ off, dat = r'.base + BitVec.ofNat 64 off ∧ off + len ≤ r'.len) :
    UpdArgs F s (sA s₀ F.stWO) dat len := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  obtain bs : Region.Sub (below s.sp F.H.F) (stk F s₀) := by rw [h.kr.sp]; exact below_stk hp (by omega_using [hX])
  obtain pw : Region.Sub (sR s₀ F.stWO F.H.S) (frR F s₀) := part_sub (by omega_using [hl])
  refine ⟨h0, h2, h3, hd, by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega_using [hX, this],
    ((f_s hp).sub_left pw).symm.sub_left bs, hs.sub_left bs, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hcd
    · exact ⟨frR F s₀, List.mem_append_right _ (fr_wr hp h.kr.wr), F.stWO, rfl,
        by show F.stWO + F.H.S ≤ F.frB; omega_using [hl]⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    exact ⟨frR F s₀, fr_wr hp h.kr.wr, F.stWO, rfl, by show F.stWO + F.H.S ≤ F.frB; omega_using [hl]⟩

/-- `update` of the working state, from `m`, with the `len` bytes at `dat`. -/
theorem updW_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat} {m : List Byte}
    (ha : UpdArgs F s (sA s₀ F.stWO) dat len)
    (hm : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) (h1 : s.gpr .a1 = BitVec.ofNat 64 m.length) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (m ++ bytesAt s.mem dat len) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hX := hz.X
  refine upd_call hF.hH ha fun t a hu => ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide))
    a.frame fun r hr => ?_, hu m hm h1⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega_using [hl]⟩
  · exact .inr (.inr ⟨F.H.F, by rw [h.kr.sp], by omega_using [hX]⟩)

/-- The salt absorbed into the working state. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad)) (h0 : s.gpr .a0 = sA s₀ F.stWO)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 F.H.B) (h2 : s.gpr .a2 = salt s₀) (h3 : s.gpr .a3 = s₀.gpr .a3) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  obtain hz := sizes hF; have hl := layout (F := F)
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine WP.mono (updW_ok hp h (updW_args hp h h0 h2 (by rw [h3]) (hp.f_sa.symm.sub_right (part_sub (by omega_using [hl])))
      hp.b_sa ⟨saltR s₀, List.mem_append_left _ (by rw [h.kr.rd, hp.rd]; simp), 0, by simp, by simp⟩) hr
    (by rw [h1, xorPad_length, hK])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [h.kr.saltBytes hp] at hu

end

/-! ## `INT (i)` -/

theorem byte_shift (i n : Nat) (hi : i < 2 ^ 64) :
    (BitVec.ofNat 64 i >>> n).setWidth 8 = BitVec.ofNat 8 (i / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hi]

theorem write4 (m : Mem) (q : Addr) (b₀ b₁ b₂ b₃ : Byte) :
    (((m.writeW (q + BitVec.ofNat 64 0) b₀).writeW (q + BitVec.ofNat 64 1) b₁).writeW (q + BitVec.ofNat 64 2)
      b₂).writeW (q + BitVec.ofNat 64 3) b₃ = writeBytes m q [b₀, b₁, b₂, b₃] := by
  rw [show [b₀, b₁, b₂, b₃] = (([] ++ [b₀]) ++ [b₁]) ++ [b₂] ++ [b₃] from rfl,
    VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp),
    VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp),
    VG.WriteBytes.writeBytes_nil]
  rfl

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `INT (k + 1)`, and `update`'s arguments for it. -/
theorem b3_ok {k : Nat} (hk : k + 1 < 2 ^ 32) {s : State} (h : Inv hF s₀ k s) {m : List Byte}
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) m ∧ bytesAt t.mem (sA s₀ F.intO) 4 = Spec.Pbkdf2.int (k + 1) ∧
      t.gpr .a0 = sA s₀ F.stWO ∧ t.gpr .a1 = BitVec.ofNat 64 (F.H.B + sl s₀) ∧ t.gpr .a2 = sA s₀ F.intO ∧
      t.gpr .a3 = BitVec.ofNat 64 4 := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  obtain e : ∀ j, s.gpr .s1 + BitVec.ofNat 64 (F.intO + j) = sA s₀ F.intO + BitVec.ofNat 64 j := fun j => by
    rw [h.kr.s1, sA_add]
  obtain hin : ∀ {t : State}, t.wr = s.wr → ∀ j < 4, InRegions t.wr (sA s₀ F.intO + BitVec.ofNat 64 j) 1 :=
    fun hw j hj => by rw [sA_add]; exact in_fr hp (hw.trans h.kr.wr) (by omega_using [hl, hj]) (by omega_using [hfr])
  unfold Fns.updArgs
  refine wp_srl (by decide) fun s₁ u₁ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 0) (by omega_using [hl, hfr])
    (by rw [u₁.other _ (by decide), h.kr.s1, sA_add]; rfl) (hin (by rw [u₁.wr]) 0 (by decide)) fun s₂ m₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 1) (by omega_using [hl, hfr])
    (by rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [u₃.wr, m₂.wr, u₁.wr]) 1 (by decide)) fun s₄ m₄ => ?_
  refine wp_srl (by decide) fun s₅ u₅ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 2) (by omega_using [hl, hfr])
    (by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr]) 2 (by decide)) fun s₆ m₆ => ?_
  refine wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 3) (by omega_using [hl, hfr])
    (by rw [m₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [m₆.wr, u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr]) 3 (by decide)) fun s₇ m₇ => ?_
  refine wp_addi (by omega_using [hl, hfr]) fun s₈ u₈ => wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₉ u₉ =>
    wp_addi (by omega_using [hl, hfr]) fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain g7 : ∀ r, r ≠ .t1 → s₇.gpr r = s.gpr r := fun r hr => by
    rw [m₇.gpr, m₆.gpr, u₅.other r hr, m₄.gpr, u₃.other r hr, m₂.gpr, u₁.other r hr]
  have v7 : s.gpr .s7 = BitVec.ofNat 64 (k + 1) := h.s7
  obtain hk64 : k + 1 < 2 ^ 64 := by omega_using [hk]
  -- The memory.
  obtain ne : Reg.s7 ≠ .t1 := by decide
  obtain v1 : s₁.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 24 := by rw [u₁.gpr, v7]
  obtain v3 : s₃.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 16 := by rw [u₃.gpr, m₂.gpr, u₁.other _ ne, v7]
  obtain v5 : s₅.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 8 := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ ne, m₂.gpr, u₁.other _ ne, v7]
  obtain v6 : s₆.gpr .s7 = BitVec.ofNat 64 (k + 1) := by
    rw [m₆.gpr, u₅.other _ ne, m₄.gpr, u₃.other _ ne, m₂.gpr, u₁.other _ ne, v7]
  obtain mm : s₁₁.mem = writeBytes s.mem (sA s₀ F.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, v6, m₆.mem, v5, u₅.mem, m₄.mem, v3, u₃.mem, m₂.mem, v1, u₁.mem,
      write4]
    simp only [Spec.Pbkdf2.int, byte_shift _ _ hk64, VG.Proof.Pbkdf2.RISCV64.setWidth_ofNat8]
  obtain fr : Frame [sR s₀ F.intO 4] s.mem s₁₁.mem := by
    rw [mm]; exact writeBytes_frame _ _ _ (by simp only [Spec.Pbkdf2.int]; exact Region.contains_self _ _)
  obtain g : ∀ r, r ≠ .t1 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₁₁.gpr r = s.gpr r := fun r a b c d f => by
    rw [u₁₁.other r f, u₁₀.other r d, u₉.other r c, u₈.other r b, g7 r a]
  refine ⟨h.keep hp (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, m₇.rd, m₆.rd, u₅.rd, m₄.rd, u₃.rd, m₂.rd, u₁.rd])
    (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, m₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr])
    (by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, m₇.sp, m₆.sp, u₅.sp, m₄.sp, u₃.sp, m₂.sp, u₁.sp])
    (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) fr
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨_, _, rfl, by omega_using [hl], by omega_using [hl]⟩),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hF.hH.congr s.mem s₁₁.mem _ _ (fun i hi => ?_) hr
    exact fr.bytes (R := sR s₀ F.stWO F.H.S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr])) (by show F.H.S ≤ 2 ^ 64; omega_using [hl, hfr]) hi
  · rw [mm]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s.mem (sA s₀ F.intO) (Spec.Pbkdf2.int (k + 1))
      (by simp [Spec.Pbkdf2.int])
    simpa [Spec.Pbkdf2.int] using this
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s1]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s2]
    obtain hsum : F.H.B + sl s₀ < 2 ^ 64 := by have := sl_bytes hp; have := hz.S; omega_arith
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .a3).toNat + F.H.B % 2 ^ 64) % 2 ^ 64 = (F.H.B + (s₀.gpr .a3).toNat) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B) (by omega_using [hsum]), Nat.add_comm]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s1]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]

/-- `INT (k + 1)` absorbed into the working state. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀))
    (hi : bytesAt s.mem (sA s₀ F.intO) 4 = Spec.Pbkdf2.int (k + 1))
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = BitVec.ofNat 64 (F.H.B + sl s₀))
    (h2 : s.gpr .a2 = sA s₀ F.intO) (h3 : s.gpr .a3 = BitVec.ofNat 64 4) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  obtain hsub : Region.Sub (sR s₀ F.intO 4) (frR F s₀) := part_sub (by omega_using [hl])
  refine WP.mono (updW_ok hp h (updW_args hp h h0 h2 (by rw [h3]; rfl)
      (part_disj (.inr (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr])) ((f_s hp).symm.sub_right hsub)
      ⟨frR F s₀, List.mem_append_right _ (fr_wr hp h.kr.wr), F.intO, rfl, by show F.intO + 4 ≤ F.frB; omega_using [hl]⟩)
    hr (by rw [h1, List.length_append, xorPad_length, hK, bytesAt_length])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [hi] at hu

/-- HMAC's `finalize`'s arguments. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .a0 = sA s₀ F.stWO ∧
      t.gpr .a1 = sA s₀ F.st1O ∧ t.gpr .a2 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧
      t.gpr .a3 = sA s₀ F.uO := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  unfold Fns.finArgs
  refine wp_addi (by omega_using [hl, hfr]) fun s₁ u₁ => wp_addi (by omega_using [hl, hfr]) fun s₂ u₂ =>
    wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₃ u₃ => wp_addi (by omega_using [hl, hfr]) fun s₄ u₄ =>
    WP.block_nil ?_
  obtain mm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₄.other r (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide),
        u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s2]
    obtain hsum : F.H.B + (sl s₀ + 4) < 2 ^ 64 := by have := sl_bytes hp; have := hz.S; omega_arith
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .a3).toNat + (F.H.B + 4) % 2 ^ 64) % 2 ^ 64 = (F.H.B + ((s₀.gpr .a3).toNat + 4)) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B + 4) (by omega_using [hsum])]
    congr 1; omega_using []
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]

/-- HMAC's `finalize`'s arguments. -/
theorem b6_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = sA s₀ F.st1O) (h3 : s.gpr .a3 = sA s₀ F.uO) :
    HfArgs F s (sA s₀ F.stWO) (sA s₀ F.st1O) (sA s₀ F.uO) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  obtain bs : Region.Sub (below s.sp (F.H.fbytes + F.H.F)) (stk F s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega_using [hX])
  obtain pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ 4096 → b + n ≤ 4096 →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj h₁ h₂ h₃
  obtain bp : ∀ {o n : Nat}, o + n ≤ F.frB → (below s.sp (F.H.fbytes + F.H.F)).Disjoint (sR s₀ o n) := fun h' =>
    ((f_s hp).sub_left (part_sub h')).symm.sub_left bs
  obtain cv : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun o n h' => ⟨frR F s₀, fr_wr hp h.kr.wr, o, rfl, h'⟩
  obtain cv' : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
    obtain ⟨r', hr', off, e, l⟩ := cv o n h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  refine ⟨h0, h1, h3, by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega_using [hX, this],
    pd (.inr (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]), pd (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]),
    pd (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]), bp (by omega_using [hl]), bp (by omega_using [hl]), bp (by omega_using [hl]), ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cv' F.st1O F.H.S (by omega_using [hl])
    · exact cv' F.stWO F.H.S (by omega_using [hl])
    · exact cv' F.uO F.H.D (by omega_using [hl])
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.stWO F.H.S (by omega_using [hl])
    · exact cv F.uO F.H.D (by omega_using [hl])

/-- `U₁`, with HMAC's `finalize`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = sA s₀ F.st1O)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4))) (h3 : s.gpr .a3 = sA s₀ F.uO) :
    WP isa F.callHf s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine hf_call hF (b6_args hp h h0 h1 h3) fun t a hf => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega_using [hl]⟩
    · exact .inl ⟨_, _, rfl, by omega_using [hl], by omega_using [hl]⟩
    · exact .inr (.inr ⟨_, by rw [h.kr.sp], by omega_using [hX]⟩)
  · have hl' : (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)).length = sl s₀ + 4 := by
      simp [bytesAt_length, Spec.Pbkdf2.int]
    refine hf (K0 hF s₀) _ (by rw [hK]) (by rw [hK, hl']; have := sl_bytes hp; have := hz.S; omega_arith)
      (by rw [← List.append_assoc]; exact hr) (by rw [h2, hl']) h.st.2

end

end VG.Proof.Pbkdf2.Whole.RISCV64

end

end

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: the rest of a block, and the loop

`T` starts as `U₁` and `iterate` runs the other `c - 1` steps (`b8_ok`):
`T = T_{k+1}`. As much of it as the output still needs is copied to `out`
(`outLen_ok`, `copyLoop_ok`), and the pointers and `i` advance (`tail_ok`):
`Inv` holds after `k + 1` blocks (`block_ok`), and after all of them
(`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_subi wp_li wp_add wp_sub wp_srl wp_lbu wp_sb eval_zero
  eval_nonzero ofNat_beq_zero)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `T ← U₁`, and `iterate`'s arguments. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = bytesAt s.mem (sA s₀ F.uO) F.H.D ∧
      t.gpr .a0 = sA s₀ Fns.st0O ∧ t.gpr .a1 = sA s₀ F.uO ∧ t.gpr .a2 = s₀.gpr .a4 - BitVec.ofNat 64 1 ∧
      t.gpr .a3 = sA s₀ F.tO ∧ t.gpr .a4 = sA s₀ F.frB := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  unfold Fns.iterArgs
  refine copy_ok hp h (a := F.uO) (b := F.tO) (n := F.H.D) (by omega_using [hl]) (by omega_using [hl]) (by omega_using [hl]) (by omega_using [hl])
    fun t ht g m => ?_
  refine wp_addi (by simp only [Fns.st0O]; omega_using []) fun s₁ u₁ => wp_addi (by omega_using [hl, hfr]) fun s₂ u₂ =>
    wp_subi (imm := 1) (by decide) fun s₃ u₃ => wp_addi (by omega_using [hl, hfr]) fun s₄ u₄ => wp_addi hfr fun s₅ u₅ =>
    WP.block_nil ?_
  obtain mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hn : F.H.D < 2 ^ 64 := by omega_using [hD]
  refine ⟨ht.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have fr : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    rw [mm]
    exact VG.Proof.Sha256.Stream.bytesAt_congr fun _ hi => fr.bytes (R := sR s₀ F.uO F.H.D)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr])) (by show F.H.D ≤ 2 ^ 64; omega_using [hD]) hi
  · rw [mm, m]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s.mem (sA s₀ F.tO) (bytesAt s.mem (sA s₀ F.uO) F.H.D)
      (by rw [bytesAt_length]; exact hn)
    rwa [bytesAt_length] at this
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s3]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]

end

/-- The low word of `c - 1`. -/
theorem lo_pred (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    ((x - BitVec.ofNat 64 1).setWidth 32).toNat = (x.setWidth 32).toNat - 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h ⊢
  have := x.isLt
  omega_using [h]

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `iterate`'s arguments. -/
theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h0 : s.gpr .a0 = sA s₀ Fns.st0O) (h1 : s.gpr .a1 = sA s₀ F.uO) (h3 : s.gpr .a3 = sA s₀ F.tO)
    (h4 : s.gpr .a4 = sA s₀ F.frB) : ItArgs F s (sA s₀ Fns.st0O) (sA s₀ F.uO) (sA s₀ F.tO) (sA s₀ F.frB) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB
  obtain pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ 4096 → b + n ≤ 4096 →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj h₁ h₂ h₃
  obtain cv : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun o n h' => ⟨frR F s₀, fr_wr hp h.kr.wr, o, rfl, h'⟩
  obtain cv' : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
    obtain ⟨r', hr', off, e, l⟩ := cv o n h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  obtain ci : ∃ r' ∈ s.wr, ∃ off, (sR s₀ F.frB F.itW).base = r'.base + BitVec.ofNat 64 off ∧ off + F.itW ≤ r'.len :=
    ⟨itR F s₀, it_wr hp h.kr.wr, 0, by simp, by show 0 + F.itW ≤ F.itB; omega_using [hl]⟩
  refine ⟨h0, h1, h3, h4, pd (.inl (by simp only [Fns.st0O]; omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]),
    pd (.inl (by simp only [Fns.st0O]; omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr, hib]), pd (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr]),
    pd (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr, hib]), pd (.inl (by omega_using [hl])) (by omega_using [hl, hfr]) (by omega_using [hl, hfr, hib]), ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' Fns.st0O (2 * F.H.S) (by simp only [Fns.st0O]; omega_using [hl])
    · exact cv' F.uO F.H.D (by omega_using [hl])
    · exact cv' F.tO F.H.D (by omega_using [hl])
    · obtain ⟨r', hr', off, e, l⟩ := ci; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.tO F.H.D (by omega_using [hl])
    · exact ci

/-- The other `c - 1` steps, with `iterate`: `T = T_{k+1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte}
    (hu : bytesAt s.mem (sA s₀ F.uO) F.H.D = u) (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = u)
    (h0 : s.gpr .a0 = sA s₀ Fns.st0O) (h1 : s.gpr .a1 = sA s₀ F.uO) (h2 : s.gpr .a2 = s₀.gpr .a4 - BitVec.ofNat 64 1)
    (h3 : s.gpr .a3 = sA s₀ F.tO) (h4 : s.gpr .a4 = sA s₀ F.frB) :
    WP isa F.callIt s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.tO) F.H.D = Spec.Pbkdf2.iterate (prf hF s₀) (cc s₀ - 1) u u := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  obtain hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine it_call hF (b8_args hp h h0 h1 h3 h4) fun t a hi => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨_, _, rfl, by omega_using [hl], by omega_using [hl]⟩
    · exact .inr (.inl (Region.sub_prefix (by omega_using [hl])))
  · have e1 : sA s₀ Fns.st0O + BitVec.ofNat 64 F.H.S = sA s₀ F.st1O := by rw [sA_add]; rfl
    rw [hi (K0 hF s₀) hK h.st.1 (by rw [e1]; exact h.st.2), hu, ht, h2, lo_pred _ hp.c0]

end

/-! ## Copying `T` out -/

/-- The sign bit of `a - b`, for `a, b < 2⁶³`: whether `a < b`. -/
theorem sub_sign {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 != 0) = decide (a < b) := by
  obtain e : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63).toNat = if a < b then 1 else 0 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split <;> omega_arith
  by_cases hab : a < b
  · simp only [hab, ↓reduceIte] at e
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 ≠ 0 := fun h0 => by rw [h0] at e; simp at e
    simp only [bne_iff_ne, ne_eq, this, not_false_eq_true, hab, decide_true]
  · simp only [hab, ↓reduceIte] at e
    have : (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = 0 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    rw [this]
    simp [hab]

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem ol_lt : ol s₀ < 2 ^ 38 := by
  have := hp.olD; have := (sizes hF).D; omega_arith

omit hp in
/-- Before block `k + 1`, some output is left. -/
theorem dn_lt (hD : 0 < F.H.D) {k : Nat} (hk : k < nbk s₀ (F := F)) :
    dn s₀ (F := F) k = k * F.H.D ∧ k * F.H.D < ol s₀ := by
  have := (Whole.lt_nb hD).1 hk
  exact ⟨by show min _ _ = _; omega_using [this], this⟩

/-- The bytes of `T` the output still needs, `min (ol - k D, D)`, in `t2`. -/
theorem outLen_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧
      t.gpr .t2 = BitVec.ofNat 64 (min (ol s₀ - k * F.H.D) F.H.D) := by
  obtain hD := (sizes hF).D
  obtain hol := ol_lt (hF := hF) hp
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  unfold Fns.outLen
  refine WP.seq (wp_subi (imm := F.H.D) (by omega_using [hD]) fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_)
  obtain i₃ : Inv hF s₀ k s₃ := h.keep hp (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₃.other r (by revert r; decide), u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)])
    (rs := []) (by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _) (by simp)
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain e5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by rw [h.s5, hdn]
  obtain e2 : s₃.gpr .t2 = BitVec.ofNat 64 (ol s₀ - k * F.H.D) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), e5]
  obtain e1 : s₃.gpr .t1 = (BitVec.ofNat 64 (ol s₀ - k * F.H.D) - BitVec.ofNat 64 F.H.D) >>> 63 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, e5]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by
      rw [eval_nonzero, e1, sub_sign (by omega_using [hol]) (by omega_using [hD])])
    (fun hT => WP.block_nil ⟨i₃, m₃, ?_⟩) fun hE => wp_li (by omega_using [hD]) fun s₄ u₄ => WP.block_nil
      ⟨i₃.keep hp u₄.rd u₄.wr u₄.sp (fun r hr => u₄.other r (by revert r; decide)) (rs := [])
        (by rw [u₄.mem]; exact Frame.refl _ _) (by simp), by rw [u₄.mem, m₃], ?_⟩
  · rw [e2, Nat.min_eq_left (Nat.le_of_lt (of_decide_eq_true hT))]
  · have := of_decide_eq_false hE
    rw [u₄.gpr, Nat.min_eq_right (by omega_using [this])]

end

/-- The output loop after `j` of its `n` bytes, copying from `A` to `B`. -/
structure CI (s : State) (A B : Addr) (n j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → t.gpr r = s.gpr r
  t3 : t.gpr .t3 = BitVec.ofNat 64 j
  t2 : t.gpr .t2 = BitVec.ofNat 64 (n - j)
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A j)

/-- The loop copying `n` bytes from `s1 + tO` to `s4`. -/
theorem copyLoop_ok {s : State} {n : Nat} {A B : Addr} {tO : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32)
    (ho : tO < 2048) (hA : s.gpr .s1 + BitVec.ofNat 64 tO = A) (hB : s.gpr .s4 = B)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < n, InRegions s.wr (B + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) {t : State} (h : CI s A B n 0 t) :
    WP isa (.loop (.block [.add .t4 .s1 .t3, .load .b .t1 .t4 tO, .add .t4 .s4 .t3, .store .b .t1 .t4 0,
      .addi .t3 .t3 1, .addi .t2 .t2 (-1)]) (.nonzero .t2)) t (CI s A B n n) := by
  refine WP.loop (M := isa) (fun m t => ∃ j, m = n - j ∧ j < n ∧ CI s A B n j t) ?_ n t ⟨0, rfl, hn, h⟩
  rintro m t ⟨j, rfl, hj, c⟩
  refine wp_add fun t₁ u₁ => wp_lbu (a := A + BitVec.ofNat 64 j) ho
    (by rw [u₁.gpr, c.other _ (by decide) (by decide) (by decide) (by decide), c.t3, ← hA]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, c.rd, c.wr]; exact hin j hj) fun t₂ u₂ => wp_add fun t₃ u₃ => ?_
  refine wp_sb (a := B + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), c.other _ (by decide) (by decide) (by decide) (by decide), c.t3, hB]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, c.wr]; exact hout j hj) fun t₄ m₄ => wp_addi (by decide) fun t₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun t₆ u₆ => WP.block_nil ?_
  obtain hl : (bytesAt s.mem A j).length = j := bytesAt_length _ _ _
  obtain byte : (t₃.gpr .t1).setWidth 8 = s.mem (A + BitVec.ofNat 64 j) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, c.mem, VG.Proof.Hmac.Common.writeBytes_other _ _ _
      (by rw [hl]; exact VG.Proof.Hmac.Generic.Common.not_mem_of_disjoint hd hj (Nat.le_of_lt hj) (by omega_using [hn']))]
    ext i hi; simp
  obtain c' : CI s A B n (j + 1) t₆ := by
    refine ⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, c.rd], by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr,
      u₁.wr, c.wr], by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, c.sp], fun r a b d e => ?_, ?_, ?_, ?_⟩
    · rw [u₆.other r b, u₅.other r d, m₄.gpr, u₃.other r e, u₂.other r a, u₁.other r e, c.other r a b d e]
    · rw [u₆.other _ (by decide), u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.t3]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), c.t2, Offset.ofNat_sub_ofNat (by omega_using [hj]), Nat.sub_sub]
    · rw [u₆.mem, u₅.mem, m₄.mem, byte, u₃.mem, u₂.mem, u₁.mem, c.mem,
        VG.Proof.Hmac.Generic.Common.bytesAt_snoc', ← VG.Proof.Hmac.Generic.Common.writeBytes_snoc _ _ _ _
          (by rw [hl]; omega_using [hn', hj]), hl]
  obtain hz : isa.eval (.nonzero .t2) t₆ = some (decide (n - (j + 1) ≠ 0)) := by
    rw [eval_nonzero, c'.t2, bne, ofNat_beq_zero (by omega_using [hn'])]
    simp
  by_cases hl' : n - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl'], ?_⟩
    obtain e : n = j + 1 := by omega_using [hj, hl']
    rw [e]; rw [e] at c'; exact c'
  · exact .inr ⟨by rw [hz, decide_eq_true hl'], _, by omega_using [hj], j + 1, rfl, by omega_using [hl'], c'⟩

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- The rest of a block: as much of `T` as the output needs, copied out, and
the pointers and `i` advanced. -/
theorem tail_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (sA s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block Fns.advance))) s (Inv hF s₀ (k + 1)) := by
  obtain hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  obtain hol := ol_lt (hF := hF) hp
  have hno := hp.no
  obtain ⟨hdn, hkD⟩ := dn_lt hD.1 hk
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  obtain hn : 0 < n := by omega_using [hD, hkD, en]
  obtain hkn : k * F.H.D + n ≤ ol s₀ := by omega_using [hkD, en]
  obtain hnD : n ≤ F.H.D := by omega_using [en]
  obtain hdn' : dn s₀ (F := F) (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega_using [hkD, en]
  obtain osub : Region.Sub ⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) := Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hk h) fun s₁ ⟨i₁, m₁, c₁⟩ => ?_)
  rw [en] at c₁
  unfold Fns.outLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_))
  obtain i₂ : Inv hF s₀ k s₂ := i₁.keep hp u₂.rd u₂.wr u₂.sp (fun r hr => u₂.other r (by revert r; decide))
    (rs := []) (by rw [u₂.mem]; exact Frame.refl _ _) (by simp)
  obtain eA : s₂.gpr .s1 + BitVec.ofNat 64 F.tO = sA s₀ F.tO := by rw [i₂.kr.s1]
  obtain eB : s₂.gpr .s4 = out s₀ + BitVec.ofNat 64 (k * F.H.D) := by rw [i₂.s4, hdn]
  obtain tsub : Region.Sub ⟨sA s₀ F.tO, n⟩ (frR F s₀) := part_sub (by omega_using [hl, en])
  refine WP.mono (copyLoop_ok (s := s₂) (n := n) hn (by omega_using [hD, en]) (by omega_using [hl, hfr]) eA eB
    (fun j hj => by rw [sA_add]; exact in_fr' hp i₂.kr.wr (by omega_using [hl, en, hj]) (by omega_using [hfr]))
    (fun j hj => ⟨outR s₀, out_wr hp i₂.kr.wr, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [en, hj]) (by omega_using [hk, hl, hfr, hD, hol, hno, hkD, en, hn, hkn, hnD, eA, hj])⟩)
    ((hp.f_o.sub_right osub).sub_left tsub)
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [u₂.gpr], by rw [u₂.other _ (by decide), c₁, Nat.sub_zero],
      by rw [bytesAt, List.range_zero, List.map_nil, VG.WriteBytes.writeBytes_nil]⟩) fun s₃ c₃ => ?_
  unfold Fns.advance
  refine wp_add fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ => WP.block_nil ?_
  -- Memory.
  obtain fr₃ : Frame [⟨out s₀ + BitVec.ofNat 64 (k * F.H.D), n⟩] s₂.mem s₃.mem := by
    rw [c₃.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  obtain hg : Gk hF s₀ (k + 1) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  obtain tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  obtain g6 : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → r ≠ .s4 → r ≠ .s5 → r ≠ .s7 → s₆.gpr r = s₂.gpr r := by
    intro r a b c d e f g
    rw [u₆.other r g, u₅.other r f, u₄.other r e, c₃.other r a b c d]
  refine ⟨i₂.kr.keep (by rw [u₆.rd, u₅.rd, u₄.rd, c₃.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, c₃.wr])
      (by rw [u₆.sp, u₅.sp, u₄.sp, c₃.sp])
      (fun r hr => g6 r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide)) (by rw [m₆]; exact fr₃)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.f_o.sub_right osub).sub_left (part_sub (o := 0) (n := 64) (by omega_using [hl])))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨outR s₀, by simp, osub⟩),
    i₂.st.keep (by rw [m₆]; exact fr₃) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.f_o.sub_right osub).sub_left (part_sub (by omega_using [hl]))), ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [c₃.t3, eB, hdn', BitVec.add_assoc, ← BitVec.ofNat_add]
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [c₃.t3, i₂.s5, hdn, hdn', Offset.ofNat_sub_ofNat (by omega_using [en]), Nat.sub_sub]
  · upd_simp [u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, c₃.other]
    rw [i₂.s7, ← BitVec.ofNat_add]
  · rw [hg, List.length_append, i₂.glen, tl, Nat.succ_mul]
  · rw [hdn', m₆, c₃.mem]
    obtain bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₂.mem (out s₀) (k * F.H.D)
      (bytesAt s₂.mem (sA s₀ F.tO) n) (by rw [bytesAt_length]; omega_using [hol, hkD, en])
    rw [bytesAt_length] at bw
    have ob := i₂.outB
    rw [hdn] at ob
    rw [bw, ob, VG.Proof.Hmac.Generic.Common.bytesAt_take _ _ hnD, u₂.mem, m₁, ht, hg, List.take_append,
      i₂.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₂.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₂.glen]; omega_using [])]

end

/-! ## The loop -/

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem nbk_lt : nbk s₀ (F := F) < 2 ^ 32 := by
  obtain hD := (sizes hF).D
  exact Whole.nb_lt hD.1 hp.olD

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk s₀ (F := F)) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s (Inv hF s₀ (k + 1)) := by
  obtain hk32 : k + 1 < 2 ^ 32 := by have := nbk_lt (hF := hF) hp; omega_using [hk, this]
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp h) fun s₁ ⟨i₁, r₁, a0, a1, a2, a3⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp i₁ r₁ a0 a1 a2 a3) fun s₂ ⟨i₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp hk32 i₂ r₂) fun s₃ ⟨i₃, r₃, n₃, c0, c1, c2, c3⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp i₃ r₃ n₃ c0 c1 c2 c3) fun s₄ ⟨i₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp i₄) fun s₅ ⟨i₅, m₅, d0, d1, d2, d3⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp i₅ (by rw [m₅]; exact r₄) d0 d1 d2 d3) fun s₆ ⟨i₆, u₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp i₆) fun s₇ ⟨i₇, hu, ht, e0, e1, e2, e3, e4⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp i₇ (hu.trans u₆) (ht.trans u₆) e0 e1 e2 e3 e4) fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hk i₈ (by rw [t₈]; rfl)

include hF in
/-- The bytes of output left, while some are. -/
theorem left_ne {k : Nat} (hk : k ≤ nbk s₀ (F := F)) :
    (BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k) != 0) = decide (k < nbk s₀ (F := F)) := by
  obtain hD := (sizes hF).D
  obtain hol := ol_lt (hF := hF) hp
  rw [bne, ofNat_beq_zero (by omega_using [hol])]
  obtain e := Whole.lt_nb (D := F.H.D) (ol := ol s₀) hD.1 (k := k)
  by_cases h : k < nbk s₀ (F := F)
  · have h1 : k * F.H.D < ol s₀ := e.1 h
    obtain h2 : dn s₀ (F := F) k = k * F.H.D := Nat.min_eq_left (Nat.le_of_lt h1)
    rw [h2]; simp only [h, decide_true]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    omega_using [h1]
  · have hk' : k = nbk s₀ (F := F) := by omega_using [hk, h]
    obtain dn' : dn s₀ (F := F) k = ol s₀ := by rw [hk']; exact Whole.done_nb hD.1
    rw [dn', Nat.sub_self]; simp [h]

/-- The blocks of the output, from `Inv 0`: `Inv` after all of them. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) :
    WP isa (.ite (.zero .s5) (.block []) (.loop F.block (.nonzero .s5))) s (Inv hF s₀ (nbk s₀ (F := F))) := by
  obtain hD := (sizes hF).D
  obtain hol := ol_lt (hF := hF) hp
  obtain e5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀) := by
    rw [h.s5]; congr 1; show _ - min (0 * F.H.D) _ = _; simp
  refine WP.ite (decide (ol s₀ = 0)) (by rw [eval_zero, e5, ofNat_beq_zero (by omega_using [hol])])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : nbk s₀ (F := F) = 0 := (Whole.nb_zero hD.1).2 (of_decide_eq_true h0)
    rw [this]; exact h
  · have hn : 0 < nbk s₀ (F := F) := by
      have : nbk s₀ (F := F) ≠ 0 := fun h' => of_decide_eq_false h0 ((Whole.nb_zero hD.1).1 h')
      omega_using [this]
    refine WP.loop (M := isa) (fun m t => ∃ k, m = nbk s₀ (F := F) - k ∧ k < nbk s₀ (F := F) ∧ Inv hF s₀ k t) ?_
      _ s ⟨0, rfl, hn, h⟩
    rintro m t ⟨k, rfl, hk, i⟩
    refine WP.mono (block_ok hp hk i) fun t' i' => ?_
    obtain hz : isa.eval (.nonzero .s5) t' = some (decide (k + 1 < nbk s₀ (F := F))) := by
      rw [eval_nonzero, i'.s5, left_ne (hF := hF) hp (by omega_using [hk])]
    by_cases hl : k + 1 < nbk s₀ (F := F)
    · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega_using [hk], k + 1, rfl, hl, i'⟩
    · refine .inl ⟨by rw [hz, decide_eq_false hl], ?_⟩
      obtain e : k + 1 = nbk s₀ (F := F) := by omega_using [hk, hl]
      rw [← e]; exact i'

end

end VG.Proof.Pbkdf2.Whole.RISCV64

end

end

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: correctness

`i = 1` and no output written start the loop (`loopInit_ok`); after it,
`out` holds `T₁ ‖ … ‖ T_l` up to `out_len` bytes, which is PBKDF2's result
(`Whole.pbkdf2_eq`), and our caller's registers are restored (`main_ok`).
In its two frames, `pbkdf2` meets `pbkR` (`correct`), from the state its
inner frame's body starts in (`pre_alloc`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem restorable : Spill.Restorable .s1 Fns.restList := by decide

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
/-- `i = 1`: `Inv` before the first block. -/
theorem loopInit_ok {s : State} (h : Keyed hF s₀ s) : WP isa (.block Fns.loopInit) s (Inv hF s₀ 0) := by
  unfold Fns.loopInit
  refine wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_
  have d0 : dn s₀ (F := F) 0 = 0 := by show min (0 * F.H.D) _ = 0; simp
  refine ⟨h.kr.upd (by decide) u₁, by rw [u₁.mem]; exact h.st,
    by rw [u₁.other _ (by decide), h.s4, d0]; simp,
    by rw [u₁.other _ (by decide), h.s5, d0]; simp, by rw [u₁.gpr], by rw [Nat.zero_mul]; rfl, ?_⟩
  rw [d0]; rfl

/-- `pbkdf2` in its frames: our caller's registers are restored, and `out`
holds the derived key. -/
theorem main_ok : WP isa F.main s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
      bytesAt s'.mem (out s₀) (ol s₀) = (Gk hF s₀ (nbk s₀ (F := F))).take (ol s₀) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  unfold Fns.main
  refine WP.seq (WP.mono (prologue_ok hF hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hi_ok' hF hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loopInit_ok h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.mono (Spill.restore_wp (b := .s1) (l := Fns.restList) (by omega_using [hp.al]) h₄.kr.s1
    (by decide) restorable
    (fun q hq => in_fr' hp h₄.kr.wr (by
      simp only [Fns.restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_using [hl]) (by omega_using [hfr]))
    (h₄.kr.saved.sub (by decide))) fun s₅ hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, h₄.kr.sp],
      by rw [hr.wr, h₄.kr.wr], ?_⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inr (h₄.kr.nv _ (by simp)), .inl (by decide), .inl (by decide), .inl (by decide),
      .inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide), .inr (h₄.kr.nv _ (by simp)),
      .inr (h₄.kr.nv _ (by simp)), .inr (h₄.kr.nv _ (by simp)), .inr (h₄.kr.nv _ (by simp))]
  · exact hr.gpr_of (.inl (by decide))
  · rw [hr.mem]
    have e := h₄.outB
    rwa [show dn s₀ (F := F) (nbk s₀ (F := F)) = ol s₀ from Whole.done_nb hD.1] at e

end

/-! ## The frames -/

/-- The state the inner frame's body starts in, from `pbkdf2`'s precondition. -/
theorem pre_alloc (hF : FnsOK F) {s : State} (hp : (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pre s) :
    Pre F (allocd F.frB (allocd F.itB s)) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB; have hX := hz.X
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hp
  rw [hF.hH.hD] at h14
  have hsp : (allocd F.frB (allocd F.itB s)).sp = s.sp - BitVec.ofNat 64 (F.itB + F.frB) := by
    simp only [allocd]; rw [BitVec.ofNat_add, Offset.sub_add_eq]
  have hspN : (s.sp - BitVec.ofNat 64 (F.itB + F.frB)).toNat = s.sp.toNat - (F.itB + F.frB) :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega_using [h6]) (by omega_using [hfr, hib])
  have hit : s.sp - BitVec.ofNat 64 F.itB =
      s.sp - BitVec.ofNat 64 (F.itB + F.frB) + BitVec.ofNat 64 F.frB := by
    rw [Offset.sub_ofNat_eq s.sp (a := F.itB) (b := F.itB + F.frB) (by omega_using []), Nat.add_sub_cancel_left]
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 (F.itB + F.frB), F.frB⟩ (below s.sp (F.itB + F.frB + F.X)) :=
    Offset.sub_below s.sp (by omega_using []) (by omega_using [])
  have subI : Region.Sub ⟨s.sp - BitVec.ofNat 64 F.itB, F.itB⟩ (below s.sp (F.itB + F.frB + F.X)) :=
    Offset.sub_below s.sp (by omega_using []) (by omega_using [])
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 (F.itB + F.frB)) F.X) (below s.sp (F.itB + F.frB + F.X)) := by
    have := below_body' s.sp (F.itB + F.frB) F.X
    rwa [Nat.add_comm F.X] at this
  have subI' : Region.Sub (itR F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub ⟨(allocd F.frB (allocd F.itB s)).sp + BitVec.ofNat 64 F.frB, F.itB⟩ _
    rw [hsp, ← hit]; exact subI
  have subF' : Region.Sub (frR F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub ⟨(allocd F.frB (allocd F.itB s)).sp, F.frB⟩ _
    rw [hsp]; exact subF
  have subS' : Region.Sub (stk F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub (below (allocd F.frB (allocd F.itB s)).sp F.X) _
    rw [hsp]; exact subS
  refine ⟨h1, ?_, h3, h4, h7.sub_left subF', h8.sub_left subF', h9.sub_left subF', h7.sub_left subI',
    h8.sub_left subI', h9.sub_left subI', ?_, ?_, ?_, h7.sub_left subS', h8.sub_left subS', h9.sub_left subS',
    h10, h11, h12, h13, h14⟩
  · show (⟨(allocd F.frB (allocd F.itB s)).sp, F.frB⟩ : Region) :: ⟨s.sp - BitVec.ofNat 64 F.itB, F.itB⟩ ::
      s.wr = _
    rw [h2, hit, ← hsp]; rfl
  · rw [hsp, hspN]; omega_using [hl, h5]
  · rw [hsp, hspN]; omega_using [h6]
  · rw [hsp, hspN]; have := s.sp.isLt; omega_using [hfr, hib]

variable (hF : FnsOK F)

/-- `pbkdf2`, with its frames. -/
theorem correct {s : State} (hp : (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pre s) :
    WP isa F.pbkdf2 s fun s' => abiPreserved s s' ∧ (pbkR hF.hH.SH (F.itB + F.frB + F.X)).post s s' := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB; have hD := hz.D
  have hsp : F.itB + F.frB + F.X ≤ s.sp.toNat := hp.2.2.2.2.2.1
  have hal : s.sp.toNat % 16 = 0 := hp.2.2.2.2.1
  have hspN : (allocd F.itB s).sp.toNat = s.sp.toNat - F.itB :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega_using [hsp]) (by omega_using [hib])
  have p := pre_alloc hF hp
  unfold Fns.pbkdf2
  refine WP.alloc ⟨by have := hF.itW0; omega_using [hl, this], hib, hl.2.2.2.2.2.2.2.2.2.2⟩ (by omega_using [hsp])
    (WP.alloc ⟨by omega_using [hl], hfr, hl.2.2.2.2.2.2.2.2.1⟩ (by rw [hspN]; omega_using [hsp])
      (WP.mono (main_ok (hF := hF) p) fun s' ⟨hk, hra, hsp', hwr, hb⟩ m₁ _ f₁ m₂ _ f₂ => ?_))
  refine ⟨⟨fun r hr => hk r hr, ?_, hra⟩, ?_⟩
  · show s'.sp + BitVec.ofNat 64 F.frB + BitVec.ofNat 64 F.itB = s.sp
    rw [hsp']; simp only [allocd, BitVec.sub_add_cancel]
  show _ = some (bytesAt m₂ (out s) (ol s))
  -- The two `free`s lose the frames' bytes, which lie apart from the output.
  have e : bytesAt m₂ (out s) (ol s) = bytesAt s'.mem (out s) (ol s) := List.map_congr_left fun i hi =>
    (lost_byte f₂ (R := outR s) ((hp.2.2.2.2.2.2.2.2.1).symm.sub_right
      (Offset.sub_below _ (by omega_using []) (by omega_using []))) (List.mem_range.mp hi)).trans
    (lost_byte f₁ (R := outR s) p.f_o.symm (List.mem_range.mp hi))
  rw [e, show out s = out (allocd F.frB (allocd F.itB s)) from rfl, show ol s = ol (allocd F.frB (allocd F.itB s)) from rfl,
    hb]
  refine Whole.pbkdf2_eq _ _ (by rw [hF.hH.hD]; exact p.olD) ?_
  rw [hF.hH.hD]
  rfl

end VG.Proof.Pbkdf2.Whole.RISCV64
