module

public import VerifiedGarbage.Proof.Hkdf.RISCV64.Key
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Hkdf.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# HKDF on RISC-V: `vg_hkdf_expand`, correct

The contract the proof is written against (`expandR`), for the table `hmac`
of one hash function `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `expand(key, info, info_len, out, out_len, hmac)` writes
HKDF-Expand's `out_len` bytes to `out`, for every pseudorandom key the
states at `key` are keyed with (`Spec.Hkdf.Keyed`). In its frame (`eFr`
bytes: the save area, the working state, `T(i)` and the counter's byte), the
prologue saves our caller's registers and keeps the arguments, `D`, `B`,
the length of `T(i - 1)` and the counter in callee-saved registers
(`pro_ok`, from which on `ER` holds). Each block (`block_ok`) makes the
working state the inner state at `key` (a copy of its hash value), absorbs
`T(i - 1)`, `info` and the counter, finalizes with the outer state at
`key + 192` into `T(i)` in the frame, and copies its first `min(D, rem)`
bytes to `out`; before block `i + 1`, `out`'s first `min(i D, L)` bytes are
`T(1) ‖ … ‖ T(i)`'s (`EI`). The blocks run while bytes of `out` are left
(`loop_ok`), and the epilogue restores our caller's registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.RISCV64.Expand

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_add wp_sub wp_sltu wp_li wp_addSp wp_ld wp_sd wp_sb)
open VG.Impl.Hkdf.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns tcall)
open VG.Proof.HmacTable.RISCV64 (HVar TabOK TabMem)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- `expand(key, info, info_len, out, out_len, hmac)`, with `N` bytes of
stack, for the table `hmac` of `w`, whose functions an indirect call of `f`'s
reaches, with the addresses of the functions `ns` public. -/
def expandR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let info : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let out : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let tab : Region := ⟨s.gpr .a5, 48⟩
    let stk : Region := below s.sp N
    s.rd = [key, info, tab] ∧ s.wr = [out] ∧ (s.gpr .a4).toNat ≤ 255 * w.H.D ∧
      key.Disjoint out ∧ info.Disjoint out ∧ tab.Disjoint out ∧
      s.sp.toNat % 16 = 0 ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint key ∧ stk.Disjoint info ∧ stk.Disjoint out ∧ stk.Disjoint tab ∧
      (s.gpr .a0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat % 8 = 0 ∧
      TabMem w s.syms (s.gpr .a5) s.mem ∧
      s.mem.readW (s.gpr .a5 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      s.mem.readW (s.gpr .a5 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B ∧ TabOK w f s.syms
  post s s' := ∀ prk, Spec.Hkdf.Keyed w.hH.SH s.mem (s.gpr .a0) prk →
    Spec.Hkdf.expand w.hH.SH.H w.H.D prk (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat) (s.gpr .a4).toNat =
      some (bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_expand` uses: its frame, and below it what HMAC's
functions use. -/
def eStack : Nat := eFr + 512

section
variable (s₀ : State)

/-- The arguments, on entry to the frame's body. -/
abbrev key : Addr := s₀.gpr .a0
abbrev info : Addr := s₀.gpr .a1
abbrev infoLen : Nat := (s₀.gpr .a2).toNat
abbrev out : Addr := s₀.gpr .a3
abbrev outLen : Nat := (s₀.gpr .a4).toNat
abbrev tab : Addr := s₀.gpr .a5

/-- An address in the frame. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o

abbrev frR : Region := ⟨s₀.sp, eFr⟩
abbrev keyR : Region := ⟨key s₀, 384⟩
abbrev infoR : Region := ⟨info s₀, infoLen s₀⟩
abbrev outR : Region := ⟨out s₀, outLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩
abbrev stk : Region := below s₀.sp 512

/-- The regions the frame's body writes. -/
abbrev wrs : List Region := [frR s₀, outR s₀, stk s₀]

end

/-- The state the frame's body starts in. -/
structure Pre (w : HVar) (f : Fns) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, infoR s₀, tabR s₀]
  wr : s₀.wr = [frR s₀, outR s₀]
  ol : outLen s₀ ≤ 255 * w.H.D
  k_o : (keyR s₀).Disjoint (outR s₀)
  i_o : (infoR s₀).Disjoint (outR s₀)
  t_o : (tabR s₀).Disjoint (outR s₀)
  f_k : (frR s₀).Disjoint (keyR s₀)
  f_i : (frR s₀).Disjoint (infoR s₀)
  f_o : (frR s₀).Disjoint (outR s₀)
  f_t : (frR s₀).Disjoint (tabR s₀)
  b_k : (stk s₀).Disjoint (keyR s₀)
  b_i : (stk s₀).Disjoint (infoR s₀)
  b_o : (stk s₀).Disjoint (outR s₀)
  b_t : (stk s₀).Disjoint (tabR s₀)
  b_f : (stk s₀).Disjoint (frR s₀)
  al : s₀.sp.toNat % 16 = 0
  sp : 512 ≤ s₀.sp.toNat
  top : s₀.sp.toNat + eFr ≤ 2 ^ 64
  nk : (key s₀).toNat + 384 ≤ 2 ^ 64
  ni : (info s₀).toNat + infoLen s₀ ≤ 2 ^ 64
  no : (out s₀).toNat + outLen s₀ ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  ta : (tab s₀).toNat % 8 = 0
  tmem : TabMem w s₀.syms (tab s₀) s₀.mem
  tD : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B
  tok : TabOK w f s₀.syms

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (expandR w f ns eStack).pre s) : Pre w f (allocd eFr s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := hp
  have hfr : eFr = 368 := rfl
  have hN : eStack = eFr + 512 := rfl
  obtain hspN : (s.sp - BitVec.ofNat 64 eFr).toNat = s.sp.toNat - eFr :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hN] at h8; omega_using [h8]) (by omega_using [hfr])
  obtain subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 eFr, eFr⟩ (below s.sp eStack) :=
    Offset.sub_below s.sp (by rw [hN]; omega_using []) (by rw [hN]; omega_using [])
  obtain subS : Region.Sub (below (s.sp - BitVec.ofNat 64 eFr) 512) (below s.sp eStack) := by
    have := below_body' s.sp eFr 512
    rwa [Nat.add_comm 512, ← hN] at this
  refine ⟨h1, by show (⟨s.sp - BitVec.ofNat 64 eFr, eFr⟩ : Region) :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h6,
    h9.sub_left subF, h10.sub_left subF, h11.sub_left subF, h12.sub_left subF,
    h9.sub_left subS, h10.sub_left subS, h11.sub_left subS, h12.sub_left subS, ?_, ?_, ?_, ?_,
    h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
  · show (below (s.sp - BitVec.ofNat 64 eFr) 512).Disjoint ⟨s.sp - BitVec.ofNat 64 eFr, eFr⟩
    exact (Offset.base_disjoint_below _ (by have := s.sp.isLt; rw [hN] at h8; omega_arith)).symm
  · show (s.sp - BitVec.ofNat 64 eFr).toNat % 16 = 0
    rw [hspN]; omega_using [hfr, h7]
  · show 512 ≤ (s.sp - BitVec.ofNat 64 eFr).toNat
    rw [hspN]; rw [hN] at h8; omega_using [h8]
  · show (s.sp - BitVec.ofNat 64 eFr).toNat + eFr ≤ 2 ^ 64
    rw [hspN]; have := s.sp.isLt; rw [hN] at h8; omega_using [hfr]

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the end of the prologue on. -/
structure ER (w : HVar) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  s1 : t.gpr .s1 = s₀.sp
  s3 : t.gpr .s3 = info s₀
  s4 : t.gpr .s4 = s₀.gpr .a2
  s6 : t.gpr .s6 = tab s₀
  s7 : t.gpr .s7 = BitVec.ofNat 64 w.H.D
  s8 : t.gpr .s8 = BitVec.ofNat 64 w.H.B
  s10 : t.gpr .s10 = key s₀
  s11 : t.gpr .s11 = s₀.gpr .s11
  saved : Spill.Saved s₀.sp s₀.gpr saved t.mem
  frame : Frame (wrs s₀) s₀.mem t.mem

/-- The registers `ER` fixes. -/
abbrev kregs : List Reg := [.s1, .s3, .s4, .s6, .s7, .s8, .s10, .s11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_in : ∀ q ∈ saved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 96 := by
  intro q hq
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A part of the frame after the save area, `out`, or the stack below the
frame. -/
def Wk (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 96 ≤ o ∧ o + n ≤ eFr) ∨ Region.Sub r (outR s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ 512

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk s₀ r) :
    Region.Disjoint ⟨s₀.sp + BitVec.ofNat 64 0, 96⟩ r ∧ ∃ r' ∈ wrs s₀, Region.Sub r r' := by
  have hfr : eFr = 368 := rfl
  have sv : Region.Sub ⟨s₀.sp + BitVec.ofNat 64 0, 96⟩ (frR s₀) := Offset.sub_base _ (by omega_using [hfr])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨Offset.disjoint _ (.inl (by omega_using [h₁])) (by decide) (by omega_using [h₂, hfr]),
      _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨(hp.f_o.sub_left sv).sub_right h, _, by simp, h⟩
  · have hb : Region.Sub (below s₀.sp n) (stk s₀) := Offset.below_mono _ hn (by decide)
    exact ⟨(hp.b_f.symm.sub_left sv).sub_right hb, _, by simp, hb⟩

theorem ER.keep {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk s₀ r) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4, (hg _ (by simp)).trans h.s6,
    (hg _ (by simp)).trans h.s7, (hg _ (by simp)).trans h.s8, (hg _ (by simp)).trans h.s10,
    (hg _ (by simp)).trans h.s11,
    h.saved.frame_in saved_in hf fun r hr => (Wk.ok hp (hw r hr)).1,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem ER.same {t t' : State} (h : ER w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : ER w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4, (hg _ (by simp)).trans h.s6,
    (hg _ (by simp)).trans h.s7, (hg _ (by simp)).trans h.s8, (hg _ (by simp)).trans h.s10,
    (hg _ (by simp)).trans h.s11, by rw [hm]; exact h.saved, by rw [hm]; exact h.frame⟩

omit hp in
theorem ER.upd {t t' : State} (h : ER w s₀ t) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd t t' d v) (hsy : t'.syms = t.syms) : ER w s₀ t' :=
  h.same u.rd u.wr u.sp hsy (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-- A part of the frame is in the writable regions. -/
theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ eFr) : InRegions t.wr (sA s₀ o) n :=
  ⟨_, by rw [hwr, hp.wr]; exact List.mem_cons_self,
    Offset.contains_base _ h (by have : eFr = 368 := rfl; omega_using [h, this])⟩

theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ eFr) :
    InRegions (t.rd ++ t.wr) (sA s₀ o) n :=
  let ⟨r, hr, hc⟩ := in_frw hp hwr h; ⟨r, List.mem_append_right _ hr, hc⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem ER.bytes {t : State} (hk : ER w s₀ t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

/-- The bytes of `key`'s and `info`'s regions are those on entry. -/
theorem ER.keyB {t : State} (hk : ER w s₀ t) {o n : Nat} (hon : o + n ≤ 384) (i : Nat) (hi : i < n) :
    t.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  have hs : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, n⟩ (keyR s₀) := Offset.sub_base _ hon
  exact hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, n⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_k.symm.sub_left hs
    · exact hp.k_o.sub_left hs
    · exact hp.b_k.symm.sub_left hs) (by show n ≤ 2 ^ 64; omega_using [hon]) hi

theorem ER.infoB {t : State} (hk : ER w s₀ t) : bytesAt t.mem (info s₀) (infoLen s₀) = bytesAt s₀.mem (info s₀) (infoLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_o
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .a2).isLt)

/-- A word of the table is as on entry. -/
theorem ER.tabW {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by have := hp.nt; omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.f_t.symm
      · exact hp.t_o
      · exact hp.b_t.symm) (by decide)

theorem tin {t : State} (hk : ER w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    InRegions (t.rd ++ t.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
  ⟨tabR s₀, List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp),
    Offset.contains_base _ ho (by have := hp.nt; omega_using [ho])⟩

theorem tal {o : Nat} (ho : o % 8 = 0) (ho' : o + 8 ≤ 48) : (tab s₀ + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.ta; have := hp.nt; have := ho'; omega_arith

end

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-! ## The loop's invariant -/

/-- The length of `T(k)`: none for `T(0)`, `D` after. -/
abbrev pl (w : HVar) (k : Nat) : Nat := if k = 0 then 0 else w.H.D

/-- `info`. -/
abbrev infoOf (s₀ : State) : List Byte := bytesAt s₀.mem (info s₀) (infoLen s₀)

/-- The pseudorandom keys the states at `key` are keyed with. -/
abbrev Keyd (w : HVar) (s₀ : State) (prk : List Byte) : Prop := Spec.Hkdf.Keyed w.hH.SH s₀.mem (key s₀) prk

/-- The blocks of `out` written after `k` blocks. -/
abbrev done (w : HVar) (s₀ : State) (k : Nat) : Nat := min (k * w.H.D) (outLen s₀)

/-- Before block `k + 1`: the registers and memory kept, `out`'s first
`done` bytes, `T(k)` in the frame, and the registers that count. -/
structure EI (w : HVar) (s₀ : State) (k : Nat) (t : State) : Prop where
  er : ER w s₀ t
  s2 : t.gpr .s2 = out s₀ + BitVec.ofNat 64 (done w s₀ k)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (outLen s₀ - done w s₀ k)
  s9 : t.gpr .s9 = BitVec.ofNat 64 (pl w k)
  s0 : t.gpr .s0 = BitVec.ofNat 64 (k + 1)
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (done w s₀ k) =
    (Spec.Hkdf.blocks w.hH.SH.H prk (infoOf s₀) k [] 1).take (done w s₀ k)
  tb : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) (pl w k) = Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k

/-! ## The prologue -/

theorem pro_eq : expandPro = .addSp .t0 0 :: (Spill.saveCode .t0 saved ++
    [mov .s1 .t0, mov .s10 .a0, mov .s3 .a1, mov .s4 .a2, mov .s2 .a3, mov .s5 .a4, mov .s6 .a5,
      .load .d .s7 .s6 32, .load .d .s8 .s6 40, .li .s9 0, .li .s0 1]) := rfl

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem pro_ok : WP isa (.block expandPro) s₀ (EI w s₀ 0) := by
  rw [pro_eq]
  have hfr : eFr = 368 := rfl
  refine VG.RISCV64.WP.of_syms (wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_)
  obtain t0 : s₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  obtain e₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  refine Spill.save_ok (b := .t0) (by rw [t0]; omega_using [hp.al])
    (fun q hq => by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_frw hp rfl (by have := saved_in q hq; omega_using [hfr, this])) ?_
  have hm₁ : s₁.mem = s₀.mem := u₁.mem
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => ?_
  obtain a6 : s₈.gpr .s6 = tab s₀ := by
    upd_simp [u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, e₁]
  obtain rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd
  obtain wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr
  obtain mm : s₈.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr saved := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr saved = _
    rw [t0]
  obtain F₈ : Frame [⟨s₀.sp, 96⟩] s₀.mem s₈.mem := by
    rw [mm, hm₁]
    exact Spill.saveMem_frame_base (n := 96) (fun p hp' => (saved_in p hp').2) (by omega_using []) _ _ _
  obtain hrw : ∀ o, o + 8 ≤ 48 → s₈.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 =
      s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 := fun o ho =>
    F₈.readW (r := tabR s₀) (Offset.contains_base _ ho (by have := hp.nt; omega_using [ho])) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.f_t.symm.sub_right (Region.sub_prefix (by omega_using [hfr]))) (by decide)
  obtain hin : ∀ o, o + 8 ≤ 48 → ∀ s : State, s.rd = s₀.rd → InRegions (s.rd ++ s.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
    fun o ho s hrd => ⟨tabR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp),
      Offset.contains_base _ ho (by have := hp.nt; omega_using [ho])⟩
  refine wp_ld (by decide) (by rw [a6]) (tal hp (o := 32) (by decide) (by decide)) (hin 32 (by decide) _ rd₈)
    fun s₉ u₉ => wp_ld (by decide) (by rw [u₉.other _ (by decide), a6]) (tal hp (o := 40) (by decide) (by decide))
      (hin 40 (by decide) s₉ (by rw [u₉.rd, rd₈])) fun s₁₀ u₁₀ => ?_
  refine wp_li (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ => WP.block_nil fun sy => ?_
  obtain m₁₂ : s₁₂.mem = s₈.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  obtain sv : Spill.Saved s₀.sp s₀.gpr saved s₁₂.mem := by
    rw [m₁₂, mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  have er : ER w s₀ s₁₂ := ⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd]; exact rd₈,
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr]; exact wr₈,
    by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp,
    sy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sv, ?_⟩
  rotate_left
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    rw [hrw 32 (by decide)]; exact hp.tD
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    rw [u₉.mem, hrw 40 (by decide)]; exact hp.tB
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · rw [m₁₂]
    exact F₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, Region.sub_prefix (by omega_using [hfr])⟩
  refine ⟨er, ?_, ?_, ?_, ?_, fun prk _ => ?_, fun prk _ => ?_⟩
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    simp [done]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    simp [done]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    simp [pl]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · simp [done, bytesAt]
  · simp [pl, bytesAt, Proof.Hkdf.tBlock]

end

/-! ## A block -/

/-- HMAC's key, its block size. -/
theorem blockKey_length (w : HVar) (k : List Byte) : (blockKey w.hH.SH.H k).length = w.H.B := by
  have hB := w.hH.hB
  have hDB : w.H.D ≤ w.H.B := by have := w.hH.hD64; rcases w.hH.hB64 with h | h <;> omega_using [this, h]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [w.hH.hashLen]; omega_using [hDB]
  · omega_arith

/-- `T(k)` has `pl k` bytes. -/
theorem tBlock_len (w : HVar) (prk info : List Byte) (k : Nat) :
    (Proof.Hkdf.tBlock w.hH.SH.H prk info k).length = pl w k := by
  cases k with
  | zero => rfl
  | succ k => exact Proof.Hkdf.tBlock_length _ _ _ w.hH.hashLen k

/-- During block `k + 1`: the registers and memory kept, `out`'s first `k D`
bytes, and the registers that count. -/
structure BR (w : HVar) (s₀ : State) (k : Nat) (t : State) : Prop where
  er : ER w s₀ t
  s2 : t.gpr .s2 = out s₀ + BitVec.ofNat 64 (k * w.H.D)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D)
  s9 : t.gpr .s9 = BitVec.ofNat 64 (pl w k)
  s0 : t.gpr .s0 = BitVec.ofNat 64 (k + 1)
  lt : k * w.H.D < outLen s₀
  ob : ∀ prk, Keyd w s₀ prk → bytesAt t.mem (out s₀) (k * w.H.D) =
    Spec.Hkdf.blocks w.hH.SH.H prk (infoOf s₀) k [] 1

/-- The regions of the frame the block uses. -/
abbrev wR (w : HVar) (s₀ : State) : Region := ⟨sA s₀ eW, w.H.S⟩
abbrev tR (w : HVar) (s₀ : State) : Region := ⟨sA s₀ eT, w.H.D⟩
abbrev cR (s₀ : State) : Region := ⟨sA s₀ eC, 1⟩

/-- `K₀` of a pseudorandom key. -/
abbrev k0 (w : HVar) (prk : List Byte) : List Byte := blockKey w.hH.SH.H prk

/-- The working state represents `K₀ ⊕ ipad`, then `m`, for each
pseudorandom key the states are keyed with. -/
abbrev WS (w : HVar) (s₀ : State) (t : State) (m : List Byte → List Byte) : Prop :=
  ∀ prk, Keyd w s₀ prk → w.hH.SH.Repr t.mem (sA s₀ eW) (xorPad (k0 w prk) ipad ++ m prk)

/-- `T(k)` in the frame, for each pseudorandom key. -/
abbrev TB (w : HVar) (s₀ : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) (pl w k) = Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
/-- The block's regions, within the frame. -/
theorem wR_sub : Region.Sub (wR w s₀) (frR s₀) :=
  Offset.sub_base _ (by have := S_le w; have : eFr = 368 := rfl; simp only [eW]; omega_arith)

omit hp in
theorem tR_sub : Region.Sub (tR w s₀) (frR s₀) :=
  Offset.sub_base _ (by have := w.hH.hD64; have : eFr = 368 := rfl; simp only [eT]; omega_arith)

omit hp in
theorem cR_sub : Region.Sub (cR s₀) (frR s₀) := Offset.sub_base _ (by decide)

omit hp in
theorem w_t : (wR w s₀).Disjoint (tR w s₀) :=
  Offset.disjoint _ (.inl (by have := S_le w; simp only [eW, eT]; omega_arith))
    (by have := S_le w; simp only [eW]; omega_arith) (by have := w.hH.hD64; simp only [eT]; omega_arith)

omit hp in
theorem w_c : (wR w s₀).Disjoint (cR s₀) :=
  Offset.disjoint _ (.inl (by have := S_le w; simp only [eW, eC]; omega_arith))
    (by have := S_le w; simp only [eW]; omega_arith) (by decide)

omit hp in
theorem t_c : (tR w s₀).Disjoint (cR s₀) :=
  Offset.disjoint _ (.inl (by have := w.hH.hD64; simp only [eT, eC]; omega_arith))
    (by have := w.hH.hD64; simp only [eT]; omega_arith) (by decide)

omit hp in
/-- The stack a callee uses, within `stk`. -/
theorem below_stk {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 512) :
    Region.Sub (below t.sp n) (stk s₀) := by
  rw [ht]; exact Offset.below_mono _ hn (by decide)

/-- `info` fits HMAC's count with a block of key, `T(i - 1)` and the counter. -/
theorem info_lt : w.H.B + w.H.D + infoLen s₀ + 1 < 2 ^ 64 := by
  have d : Region.Disjoint ⟨info s₀, infoLen s₀⟩ ⟨s₀.sp - BitVec.ofNat 64 512, 512⟩ := hp.b_i.symm
  have sp := hp.sp
  have e : (s₀.sp - BitVec.ofNat 64 512).toNat = s₀.sp.toNat - 512 :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega_using [sp]) (by decide)
  have h2 : (s₀.sp - BitVec.ofNat 64 512).toNat + 512 ≤ 2 ^ 64 := by
    rw [e]; have := s₀.sp.isLt; omega_using [this, sp]
  have h := VG.Proof.Pbkdf2.Whole.len_add_le d hp.ni h2
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  have hD := w.hH.hD64
  have h' : infoLen s₀ + 512 ≤ 2 ^ 64 := h
  omega_using [h', hB, hD]

omit hp in
/-- The bytes of a region of the frame apart from `rs` are kept. -/
theorem keep_fr {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    (hR : R.len ≤ 2 ^ 64) : bytesAt m' R.base R.len = bytesAt m R.base R.len :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes hd hR hi

omit hp in
/-- The working state, as the inner state at `key`, for each pseudorandom key. -/
theorem ws_of {t : State}
    (hc : ∀ i < 64, t.mem (sA s₀ eW + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 i)) :
    WS w s₀ t fun _ => [] := by
  intro prk hK
  rw [List.append_nil]
  refine w.hH.reloc _ _ _ _ _ ?_ (fun i hi => hc i (by have := w.hH.hN; omega_using [this, hi])) hK.1
  rw [xorPad_length, blockKey_length, Nat.mod_self]

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- What the registers of `BR` keep. -/
abbrev bregs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

omit hp in
theorem BR.keep {k : Nat} {t t' : State} (h : BR w s₀ k t) (he : ER w s₀ t')
    (hg : ∀ r ∈ bregs, t'.gpr r = t.gpr r)
    (hb : bytesAt t'.mem (out s₀) (k * w.H.D) = bytesAt t.mem (out s₀) (k * w.H.D)) : BR w s₀ k t' :=
  ⟨he, (hg _ (by simp)).trans h.s2, (hg _ (by simp)).trans h.s5, (hg _ (by simp)).trans h.s9,
    (hg _ (by simp)).trans h.s0, h.lt, fun prk hK => hb.trans (h.ob prk hK)⟩

/-- `out` is apart from the frame and the stack below it. -/
theorem out_apart {o n : Nat} (h : o + n ≤ outLen s₀) {r : Region}
    (hr' : (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 96 ≤ o ∧ o + n ≤ eFr) ∨ ∃ n, r = below s₀.sp n ∧ n ≤ 512) :
    Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 o, n⟩ r := by
  have hs : Region.Sub ⟨out s₀ + BitVec.ofNat 64 o, n⟩ (outR s₀) := Offset.sub_base _ h
  rcases hr' with ⟨o', n', rfl, _, h₂⟩ | ⟨n', rfl, hn⟩
  · exact (hp.f_o.symm.sub_left hs).sub_right (Offset.sub_base _ h₂)
  · exact (hp.b_o.symm.sub_left hs).sub_right (Offset.below_mono _ hn (by decide))

/-- The copy of the inner state at `key`'s hash value to the working state. -/
theorem copy_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) :
    WP isa (.seq (.block copyArgs) (Impl.Words.RISCV64.copyAny .t0 .a4 .a5 .a6)) t fun u =>
      BR w s₀ k u ∧ TB w s₀ k u ∧ WS w s₀ u (fun _ => []) ∧ u.syms = s₀.syms := by
  have hfr : eFr = 368 := rfl
  have k₀ := h.er
  unfold copyArgs
  refine WP.seq (VG.RISCV64.WP.of_syms (wp_mv fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ =>
    wp_li (by decide) fun t₃ u₃ => WP.block_nil fun sy => ?_))
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have k₃ : ER w s₀ t₃ := k₀.same (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp]) sy (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> upd_simp [u₃.other, u₂.other, u₁.other]) m₃
  have a4 : t₃.gpr .a4 = key s₀ := by upd_simp [u₃.other, u₂.other, u₁.gpr]; exact k₀.s10
  have a5 : t₃.gpr .a5 = sA s₀ eW := by upd_simp [u₃.other, u₂.gpr, u₁.other]; rw [k₀.s1]
  have a6 : t₃.gpr .a6 = BitVec.ofNat 64 64 := by upd_simp [u₃.gpr]
  have hwk : ∀ i < 64, (sA s₀ eW + BitVec.ofNat 64 i) = sA s₀ (eW + i) := fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine VG.RISCV64.WP.of_syms (WP.mono (WP.rdwr (copyAny_ok (tmp := .t0) (src := .a4) (dst := .a5) (cnt := .a6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t₃ (N := 64) (by decide) (by decide)
    (by decide) a6 (fun i hi => ?_) (fun i hi => ?_) (fun i hi _ => ?_) (fun i hi _ => ?_) ?_))
    fun u ⟨⟨hc, hf, hkp⟩, hrd, hwr, hsp⟩ sy' => ?_)
  · rw [a4, k₃.rd, hp.rd]
    exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [a5, hwk i hi]; exact in_frw hp k₃.wr (by simp only [eW]; omega_using [hi, hfr])
  · rw [a4, k₃.rd, hp.rd]
    exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [a5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact in_frw hp k₃.wr (by simp only [eW]; omega_using [hi, hfr])
  · rw [a5, a4]
    exact Region.Disjoint.sep ((hp.f_k.sub_left (Offset.sub_base _ (by simp only [eW]; omega_using [hfr]))).sub_right
      (Region.sub_prefix (by decide : 64 ≤ 384))) (Region.contains_self _ _) (Region.contains_self _ _)
  rw [a5] at hc hf
  rw [a4] at hc
  have hwr' : Wk s₀ ⟨sA s₀ eW, 64⟩ := .inl ⟨eW, 64, rfl, by decide, by simp only [eW]; omega_using [hfr]⟩
  have ku : ER w s₀ u := k₃.keep hp hrd hwr hsp (sy'.trans rfl)
    (fun r hr => hkp.gpr (by revert r; decide)) hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hwr')
  have dfr : ∀ {R : Region}, Region.Disjoint R ⟨sA s₀ eW, 64⟩ → R.len ≤ 2 ^ 64 →
      bytesAt u.mem R.base R.len = bytesAt t₃.mem R.base R.len := fun hd hl =>
    keep_fr hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  refine ⟨h.keep ku (fun r hr => ?_) ?_, fun prk hK => ?_, ws_of fun i hi => ?_, sy'.trans (sy.trans h.er.sy)⟩
  · rw [hkp.gpr (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide),
      u₁.other r (by revert r; decide)]
  · have hl : 0 + k * w.H.D ≤ outLen s₀ := by have := h.lt; omega_using [this]
    have hd := out_apart hp (o := 0) hl (.inl ⟨eW, 64, rfl, by decide, by simp only [eW]; omega_using [hfr]⟩)
    rw [BitVec.add_zero] at hd
    exact (dfr hd (by show k * w.H.D ≤ 2 ^ 64; have : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt; omega_using [hl, this])).trans (by rw [m₃])
  · have hD := w.hH.hD64
    have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
    have hd : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ ⟨sA s₀ eW, 64⟩ :=
      Offset.disjoint _ (.inr (by simp only [eW, eT]; omega_arith)) (by simp only [eT]; omega_using [hpl])
        (by simp only [eW]; omega_arith)
    exact (dfr hd (by show pl w k ≤ 2 ^ 64; omega_using [hpl])).trans (by rw [m₃]; exact ht prk hK)
  · rw [hc i hi, m₃]
    have := ER.keyB hp k₀ (o := 0) (n := 64) (by decide) i hi
    rwa [BitVec.add_zero] at this

end

/-! ## The calls of a block -/

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- What `update`'s arguments are, for `len` bytes at `dat`. -/
structure UA (w : HVar) (s₀ : State) (dat : Addr) (len : Nat) (t : State) : Prop where
  a0 : t.gpr .a0 = sA s₀ eW
  a2 : t.gpr .a2 = dat
  a3 : (t.gpr .a3).toNat = len
  d_w : Region.Disjoint ⟨dat, len⟩ (wR w s₀)
  d_b : Region.Disjoint (below s₀.sp 512) ⟨dat, len⟩
  cov : RISCV64.Covers [⟨dat, len⟩] (t.rd ++ t.wr)

theorem upd_args {k : Nat} {t t' : State} (h : BR w s₀ k t) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    {v : Addr} (u : Upd t t' .t1 v) : UpdArgs w t' (sA s₀ eW) dat len := by
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp w.H.F) (stk s₀) := below_stk (by rw [u.sp, h.er.sp]) hx.2.2
  refine ⟨by rw [g _ (by decide), ha.a0], by rw [g _ (by decide), ha.a2], by rw [g _ (by decide), ha.a3],
    ha.d_w, by rw [u.sp, h.er.sp]; exact hp.al, by rw [u.sp, h.er.sp]; have := hp.sp; omega_using [this, hx.2.2],
    (hp.b_f.sub_left hb).sub_right wR_sub, ha.d_b.sub_left hb, ?_, ?_⟩
  · refine VG.Covers.append_left (by rw [u.rd, u.wr]; exact ha.cov) (VG.Covers.of_sub fun r hr => ?_)
    rw [u.rd, u.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, by simp, eW, rfl, by have := S_le w; have : eFr = 368 := rfl; dsimp only; simp only [eW]; omega_arith⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, h.er.wr, hp.wr]
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, by simp, eW, rfl, by have := S_le w; have : eFr = 368 := rfl; dsimp only; simp only [eW]; omega_arith⟩

/-- `update` with `len` bytes at `dat`, once the load of its address wrote
`t1`: the working state absorbs them, and `BR` and `T(k)` are kept. -/
theorem upd_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) {m : List Byte → List Byte}
    (hw : WS w s₀ t m) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    (hc : t.gpr .a1 = BitVec.ofNat 64 (w.H.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) {v : Addr} (u : Upd t t' .t1 v) (sy : t'.syms = t.syms) :
    WP isa (.call w.H.updN w.H.updC) t' fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) ∧ u'.syms = s₀.syms := by
  have hx := x_le w
  have hb : Region.Sub (below t'.sp w.H.F) (stk s₀) := below_stk (by rw [u.sp, h.er.sp]) hx.2.2
  refine VG.RISCV64.WP.of_syms <| VG.Proof.Hkdf.RISCV64.upd_call (upd_args hp h ha u) fun s' a hu sy' => ?_
  have hW : ∀ r ∈ ([⟨sA s₀ eW, w.H.S⟩] ++ [below t'.sp w.H.F] : List Region), Wk s₀ r := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨eW, w.H.S, rfl, by decide, by have := S_le w; have : eFr = 368 := rfl; simp only [eW]; omega_arith⟩
    · exact .inr (.inr ⟨_, by rw [u.sp, h.er.sp], hx.2.2⟩)
  have k' : ER w s₀ s' := (h.er.upd (by decide) u sy).keep hp a.rd a.wr a.sp sy'
    (fun r hr => a.cs r (kregs_pres r hr)) a.frame hW
  have hm : t'.mem = t.mem := u.mem
  have apart : ∀ {R : Region}, R.Disjoint (wR w s₀) → R.Disjoint (stk s₀) → R.len ≤ 2 ^ 64 →
      bytesAt s'.mem R.base R.len = bytesAt t.mem R.base R.len := fun h₁ h₂ hl =>
    (keep_fr a.frame (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂.sub_right hb) hl).trans (by rw [hm])
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  refine ⟨h.keep (k' : ER w s₀ s') (fun r hr => a.cs r (by revert r; decide) |>.trans
      (u.other r (by revert r; decide))) ?_, fun prk hK => ?_, fun prk hK => ?_, sy'.trans (sy.trans h.er.sy)⟩
  · have d₁ := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk]) (r := wR w s₀)
      (.inl ⟨eW, w.H.S, rfl, by decide, by have := S_le w; have : eFr = 368 := rfl; simp only [eW]; omega_arith⟩)
    have d₂ := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk]) (r := stk s₀)
      (.inr ⟨512, rfl, Nat.le_refl _⟩)
    rw [BitVec.add_zero] at d₁ d₂
    exact apart d₁ d₂ (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
  · have d₁ : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (wR w s₀) :=
      Offset.disjoint _ (.inr (by have := S_le w; simp only [eW, eT]; omega_arith)) (by simp only [eT]; omega_using [hpl])
        (by have := S_le w; simp only [eW]; omega_arith)
    have d₂ : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (stk s₀) :=
      (hp.b_f.symm.sub_left (Offset.sub_base _ (by have : eFr = 368 := rfl; simp only [eT]; omega_using [hpl, this])))
    exact (apart d₁ d₂ (by show pl w k ≤ 2 ^ 64; omega_using [hpl])).trans (ht prk hK)
  · have := hu _ (by rw [hm]; exact hw prk hK) (by
      rw [u.other _ (by decide), hc, List.length_append, xorPad_length, blockKey_length, hml prk])
    rwa [hm, List.append_assoc] at this

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The loads of the table's functions' addresses. -/
theorem tload1 {t : State} (k : ER w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 1)]) t fun u => Upd t u .t1 (s₀.syms w.H.updN) ∧ u.syms = t.syms :=
  tload_ok (by decide) k.s6 (tin hp k (by decide)) (tal hp rfl (by decide))
    (by rw [show (8 * 1 : Nat) = 8 from rfl, k.tabW hp (by decide)]; exact hp.tmem.2.1)

theorem tload2 {t : State} (k : ER w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 2)]) t fun u => Upd t u .t1 (s₀.syms w.hfN) ∧ u.syms = t.syms :=
  tload_ok (by decide) k.s6 (tin hp k (by decide)) (tal hp rfl (by decide))
    (by rw [show (8 * 2 : Nat) = 16 from rfl, k.tabW hp (by decide)]; exact hp.tmem.2.2)

/-- `update` with `len` bytes at `dat`, through the table. -/
theorem upd_stage {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) {m : List Byte → List Byte}
    (hw : WS w s₀ t m) {dat : Addr} {len : Nat} (ha : UA w s₀ dat len t)
    (hc : t.gpr .a1 = BitVec.ofNat 64 (w.H.B + ((m []).length)))
    (hml : ∀ prk, (m prk).length = (m []).length) :
    WP isa (tcall 1 f.upd) t fun u' => BR w s₀ k u' ∧ TB w s₀ k u' ∧
      WS w s₀ u' (fun prk => m prk ++ bytesAt t.mem dat len) ∧ u'.syms = s₀.syms := by
  unfold tcall
  refine WP.seq (WP.mono (tload1 hp h.er) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (upd_step hp h ht hw ha hc hml u sy)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, h.er.sy]; exact hp.tok.u

/-- The frame's part at `o` of `n` bytes, apart from the working state, the
stack below the frame, and covered by the regions. -/
theorem fr_ua {t : State} (k : ER w s₀ t) {o n : Nat} (h₁ : eW + w.H.S ≤ o) (h₂ : o + n ≤ eFr) :
    Region.Disjoint ⟨sA s₀ o, n⟩ (wR w s₀) ∧ Region.Disjoint (below s₀.sp 512) ⟨sA s₀ o, n⟩ ∧
      RISCV64.Covers [⟨sA s₀ o, n⟩] (t.rd ++ t.wr) := by
  have hfr : eFr = 368 := rfl
  refine ⟨Offset.disjoint _ (.inr h₁) (by omega_using [h₂, hfr]) (by have := S_le w; simp only [eW]; omega_arith),
    hp.b_f.sub_right (Offset.sub_base _ h₂), VG.Covers.one (in_fr hp k.wr h₂)⟩

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `update`'s arguments for `len` bytes at `dat`, the working state
holding `B + n` bytes (`m`). -/
structure AT (w : HVar) (s₀ : State) (k : Nat) (dat : Addr) (len n : Nat) (m : List Byte → List Byte)
    (t : State) : Prop where
  br : BR w s₀ k t
  tb : TB w s₀ k t
  ws : WS w s₀ t m
  ua : UA w s₀ dat len t
  a1 : t.gpr .a1 = BitVec.ofNat 64 (w.H.B + n)
  sy : t.syms = s₀.syms

/-- `update`'s arguments for `T(k)`. -/
theorem argsT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.block updT) t (AT w s₀ k (sA s₀ eT) (pl w k) 0 fun _ => []) := by
  have hfr : eFr = 368 := rfl
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  unfold updT
  refine (VG.RISCV64.WP.of_syms (wp_addi (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ =>
    wp_addi (by decide) fun t₃ u₃ => wp_mv fun t₄ u₄ => WP.block_nil fun sy => ?_))
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : ER w s₀ t₄ := h.er.same (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]) m₄
  have g : ∀ r ∈ bregs, t₄.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]
  have h₄ : BR w s₀ k t₄ := h.keep k₄ g (by rw [m₄])
  obtain ⟨dw, db, cov⟩ := fr_ua hp k₄ (o := eT) (n := pl w k) (by have := S_le w; simp only [eW, eT]; omega_arith)
    (by simp only [eT]; omega_using [hfr, hpl])
  have ua : UA w s₀ (sA s₀ eT) (pl w k) t₄ :=
    ⟨by upd_simp [u₄.other, u₃.other, u₂.other, u₁.gpr]; rw [h.er.s1],
      by upd_simp [u₄.other, u₃.gpr, u₂.other, u₁.other]; rw [h.er.s1],
      by upd_simp [u₄.gpr, u₃.other, u₂.other, u₁.other]; rw [h.s9, BitVec.toNat_ofNat]; omega_using [hpl],
      dw, db, cov⟩
  exact ⟨h₄, fun prk hK => by rw [m₄]; exact ht prk hK, fun prk hK => by rw [m₄]; exact hw prk hK, ua,
    by upd_simp [u₄.other, u₃.other, u₂.gpr, u₁.other]; rw [h.er.s8]; rfl, sy.trans h.er.sy⟩

/-- What `update` with `T(k)` gives. -/
abbrev PT (w : HVar) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k) ∧ u.syms = s₀.syms

theorem callT_ok {k : Nat} {t : State} (a : AT w s₀ k (sA s₀ eT) (pl w k) 0 (fun _ => []) t) :
    WP isa (tcall 1 f.upd) t (PT w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua a.a1 (fun _ => rfl))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [List.nil_append, a.tb prk hK] at this, syv⟩

/-- `update` with `T(k)`. -/
theorem stageT_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t) (hw : WS w s₀ t fun _ => []) :
    WP isa (.seq (.block updT) (tcall 1 f.upd)) t (PT w s₀ k) :=
  WP.seq (WP.mono (argsT_ok hp h ht hw) fun _ a => callT_ok hp a)

/-- `update`'s arguments for `info`. -/
theorem argsI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k) :
    WP isa (.block updI) t
      (AT w s₀ k (info s₀) (infoLen s₀) (pl w k) fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k) := by
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  unfold updI
  refine (VG.RISCV64.WP.of_syms (wp_addi (by decide) fun t₁ u₁ => wp_add fun t₂ u₂ =>
    wp_mv fun t₃ u₃ => wp_mv fun t₄ u₄ => WP.block_nil fun sy => ?_))
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : ER w s₀ t₄ := h.er.same (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]) m₄
  have g : ∀ r ∈ bregs, t₄.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]
  have h₄ : BR w s₀ k t₄ := h.keep k₄ g (by rw [m₄])
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  have ua : UA w s₀ (info s₀) (infoLen s₀) t₄ :=
    ⟨by upd_simp [u₄.other, u₃.other, u₂.other, u₁.gpr]; rw [h.er.s1],
      by upd_simp [u₄.other, u₃.gpr, u₂.other, u₁.other]; exact h.er.s3,
      by upd_simp [u₄.gpr, u₃.other, u₂.other, u₁.other]; rw [h.er.s4],
      hp.f_i.symm.sub_right wR_sub, hp.b_i,
      VG.Covers.one ⟨infoR s₀, List.mem_append_left _ (by rw [k₄.rd, hp.rd]; simp), Region.contains_self _ _⟩⟩
  refine ⟨h₄, fun prk hK => by rw [m₄]; exact ht prk hK, fun prk hK => by rw [m₄]; exact hw prk hK, ua, ?_,
    sy.trans h.er.sy⟩
  upd_simp [u₄.other, u₃.other, u₂.gpr, u₁.other]
  rw [h.er.s8, h.s9, BitVec.ofNat_add_ofNat]

/-- What `update` with `info` gives. -/
abbrev PI (w : HVar) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀) ∧ u.syms = s₀.syms

theorem callI_ok {k : Nat} {t : State}
    (a : AT w s₀ k (info s₀) (infoLen s₀) (pl w k) (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k) t) :
    WP isa (tcall 1 f.upd) t (PI w s₀ k) :=
  WP.mono (upd_stage hp a.br a.tb a.ws a.ua (by rw [a.a1, tBlock_len]) (fun prk => by rw [tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.br.er.infoB hp] at this, syv⟩

/-- `update` with `info`. -/
theorem stageI_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k) :
    WP isa (.seq (.block updI) (tcall 1 f.upd)) t (PI w s₀ k) :=
  WP.seq (WP.mono (argsI_ok hp h ht hw) fun _ a => callI_ok hp a)

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The counter's byte stored in the frame; `update`'s arguments for it. -/
theorem argsC_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.block updC) t fun u =>
      AT w s₀ k (sA s₀ eC) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++
        infoOf s₀) u ∧ bytesAt u.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)] := by
  have hfr : eFr = 368 := rfl
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  have hil := info_lt hp
  unfold updC
  refine (VG.RISCV64.WP.of_syms (wp_sb (by decide) (a := sA s₀ eC) (by rw [h.er.s1])
    (in_frw hp h.er.wr (by simp only [eC]; omega_using [hfr])) fun t₁ m₁ =>
    wp_addi (by decide) fun t₂ u₂ => wp_add fun t₃ u₃ => wp_add fun t₄ u₄ => wp_addi (by decide) fun t₅ u₅ =>
    wp_li (by decide) fun t₆ u₆ => WP.block_nil fun sy => ?_))
  have F : Frame [cR s₀] t.mem t₆.mem := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hwc : Wk s₀ (cR s₀) := .inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩
  have k₆ : ER w s₀ t₆ := h.er.keep hp (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, m₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, m₁.wr]) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, m₁.sp]) sy
    (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, m₁.gpr]) F
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hwc)
  have g : ∀ r ∈ bregs, t₆.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, m₁.gpr]
  have apart : ∀ {R : Region}, R.Disjoint (cR s₀) → R.len ≤ 2 ^ 64 →
      bytesAt t₆.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl =>
    keep_fr F (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  have h₆ : BR w s₀ k t₆ := h.keep k₆ g (by
    have d := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk]) (r := cR s₀)
      (.inl ⟨eC, 1, rfl, by decide, by simp only [eC]; omega_using [hfr]⟩)
    rw [BitVec.add_zero] at d
    exact apart d (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol]))
  have tb₆ : TB w s₀ k t₆ := fun prk hK => by
    have d : Region.Disjoint ⟨sA s₀ eT, pl w k⟩ (cR s₀) :=
      Offset.disjoint _ (.inl (by simp only [eT, eC]; omega_using [hpl])) (by simp only [eT]; omega_using [hpl])
        (by decide)
    exact (apart d (by show pl w k ≤ 2 ^ 64; omega_using [hpl])).trans (ht prk hK)
  have ws₆ : WS w s₀ t₆ fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ := fun prk hK =>
    w.hH.congr _ _ _ _ (fun i hi => F.bytes (R := wR w s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_c) (by show w.H.S ≤ 2 ^ 64; have := S_le w; omega_using [this]) hi)
      (hw prk hK)
  obtain ⟨dw, db, cov⟩ := fr_ua hp k₆ (o := eC) (n := 1) (by have := S_le w; simp only [eW, eC]; omega_arith)
    (by simp only [eC]; omega_using [hfr])
  have ua : UA w s₀ (sA s₀ eC) 1 t₆ :=
    ⟨by upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, m₁.gpr]; rw [h.er.s1],
      by upd_simp [u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, m₁.gpr]; rw [h.er.s1],
      by upd_simp [u₆.gpr]; rfl, dw, db, cov⟩
  have hbyte : bytesAt t₆.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)] := by
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁.mem, WriteBytes.writeW8_apply, ite_eq_left rfl, h.s0]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  refine ⟨⟨h₆, tb₆, ws₆, ua, ?_, sy.trans h.er.sy⟩, hbyte⟩
  · upd_simp [u₆.other, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.other, m₁.gpr]
    rw [h.er.s8, h.s9, h.er.s4]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (s₀.gpr .a2).toNat < 2 ^ 64 := (s₀.gpr .a2).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [hB, hpl] : w.H.B < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [hpl] : pl w k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hB, hpl] : w.H.B + pl w k < 2 ^ 64)]
    show (w.H.B + pl w k + infoLen s₀) % 2 ^ 64 = (w.H.B + (pl w k + infoLen s₀)) % 2 ^ 64
    rw [Nat.add_assoc]

/-- `update`'s arguments for the counter. -/
abbrev AC (w : HVar) (s₀ : State) (k : Nat) (u : State) : Prop :=
  AT w s₀ k (sA s₀ eC) 1 (pl w k + infoLen s₀) (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++
    infoOf s₀) u ∧ bytesAt u.mem (sA s₀ eC) 1 = [BitVec.ofNat 8 (k + 1)]

/-- What `update` with the counter gives. -/
abbrev PC (w : HVar) (s₀ : State) (k : Nat) (u : State) : Prop := BR w s₀ k u ∧ TB w s₀ k u ∧
  WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++
    [BitVec.ofNat 8 (k + 1)]) ∧ u.syms = s₀.syms

theorem callC_ok {k : Nat} {t : State} (a : AC w s₀ k t) : WP isa (tcall 1 f.upd) t (PC w s₀ k) :=
  WP.mono (upd_stage hp a.1.br a.1.tb a.1.ws a.1.ua
      (by rw [a.1.a1, List.length_append, tBlock_len, bytesAt_length])
      (fun prk => by rw [List.length_append, List.length_append, tBlock_len, tBlock_len]))
    fun _ ⟨hv, htv, hwv, syv⟩ => ⟨hv, htv, fun prk hK => by
      have := hwv prk hK; rwa [a.2] at this, syv⟩

/-- `update` with the counter's byte, stored in the frame first. -/
theorem stageC_ok {k : Nat} {t : State} (h : BR w s₀ k t) (ht : TB w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀) :
    WP isa (.seq (.block updC) (tcall 1 f.upd)) t (PC w s₀ k) :=
  WP.seq (WP.mono (argsC_ok hp h ht hw) fun _ a => callC_ok hp a)

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `finalize`'s arguments. -/
structure FA (w : HVar) (s₀ : State) (k : Nat) (t : State) : Prop where
  a0 : t.gpr .a0 = sA s₀ eW
  a1 : t.gpr .a1 = key s₀ + BitVec.ofNat 64 192
  a2 : t.gpr .a2 = BitVec.ofNat 64 (w.H.B + (pl w k + infoLen s₀ + 1))
  a3 : t.gpr .a3 = sA s₀ eT

/-- The outer state's region, within `key`. -/
abbrev ouR (w : HVar) (s₀ : State) : Region := ⟨key s₀ + BitVec.ofNat 64 192, w.H.S⟩

omit hp in
theorem ou_sub : Region.Sub (ouR w s₀) (keyR s₀) :=
  Offset.sub_base _ (by have := S_le w; omega_using [this])

theorem fin_args {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t) {v : Addr}
    (u : Upd t t' .t1 v) : HfArgs w t' (sA s₀ eW) (key s₀ + BitVec.ofNat 64 192) (sA s₀ eT) := by
  have hx := x_le w
  have hfr : eFr = 368 := rfl
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.fbytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, h.er.sp]) hx.2.1
  refine ⟨by rw [g _ (by decide), ha.a0], by rw [g _ (by decide), ha.a1], by rw [g _ (by decide), ha.a3],
    by rw [u.sp, h.er.sp]; exact hp.al, by rw [u.sp, h.er.sp]; have := hp.sp; omega_using [this, hx.2.1],
    (hp.f_k.sub_left wR_sub).sub_right ou_sub, w_t, (hp.f_k.symm.sub_left ou_sub).sub_right tR_sub,
    (hp.b_f.sub_left hb).sub_right wR_sub, (hp.b_k.sub_left hb).sub_right ou_sub,
    (hp.b_f.sub_left hb).sub_right tR_sub, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.rd, u.wr, h.er.rd, h.er.wr, hp.rd, hp.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨keyR s₀, by simp, 192, rfl, by have := S_le w; dsimp only; omega_using [this]⟩
    · exact ⟨frR s₀, by simp, eW, rfl, by have := S_le w; dsimp only; simp only [eW]; omega_arith⟩
    · exact ⟨frR s₀, by simp, eT, rfl, by have := w.hH.hD64; dsimp only; simp only [eT]; omega_arith⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, h.er.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨frR s₀, by simp, eW, rfl, by have := S_le w; dsimp only; simp only [eW]; omega_arith⟩
    · exact ⟨frR s₀, by simp, eT, rfl, by have := w.hH.hD64; dsimp only; simp only [eT]; omega_arith⟩

/-- `T(k + 1)` in the frame, for each pseudorandom key. -/
abbrev TF (w : HVar) (s₀ : State) (k : Nat) (t : State) : Prop :=
  ∀ prk, Keyd w s₀ prk → bytesAt t.mem (sA s₀ eT) w.H.D = Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) (k + 1)

/-- `finalize`, once the load of its address wrote `t1`: `T(k + 1)`. -/
theorem fin_step {k : Nat} {t t' : State} (h : BR w s₀ k t) (ha : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
    {v : Addr} (u : Upd t t' .t1 v) (sy : t'.syms = t.syms) :
    WP isa (.call w.hfN w.H.finalize) t' fun u' => BR w s₀ k u' ∧ TF w s₀ k u' ∧ u'.syms = s₀.syms := by
  have hx := x_le w
  have hfr : eFr = 368 := rfl
  have hb : Region.Sub (below t'.sp (w.H.fbytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, h.er.sp]) hx.2.1
  refine VG.RISCV64.WP.of_syms <| VG.Proof.Hkdf.RISCV64.hf_call (fin_args hp h ha u) fun s' a hf sy' => ?_
  have hW : ∀ r ∈ ([⟨sA s₀ eW, w.H.S⟩, ⟨sA s₀ eT, w.H.D⟩] ++ [below t'.sp (w.H.fbytes + w.H.F)] : List Region),
      Wk s₀ r := fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨eW, w.H.S, rfl, by decide, by have := S_le w; simp only [eW]; omega_arith⟩
    · exact .inl ⟨eT, w.H.D, rfl, by decide, by have := w.hH.hD64; simp only [eT]; omega_arith⟩
    · exact .inr (.inr ⟨_, by rw [u.sp, h.er.sp], hx.2.1⟩)
  have k' : ER w s₀ s' := (h.er.upd (by decide) u sy).keep hp a.rd a.wr a.sp sy'
    (fun r hr => a.cs r (kregs_pres r hr)) a.frame hW
  have hm : t'.mem = t.mem := u.mem
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  have hil := info_lt hp
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  refine ⟨h.keep k' (fun r hr => a.cs r (by revert r; decide) |>.trans (u.other r (by revert r; decide))) ?_,
    fun prk hK => ?_, sy'.trans (sy.trans h.er.sy)⟩
  · have dO : ∀ r ∈ ([⟨sA s₀ eW, w.H.S⟩, ⟨sA s₀ eT, w.H.D⟩] ++ [below t'.sp (w.H.fbytes + w.H.F)] : List Region),
        Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩ r := fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact out_apart hp (by omega_using [hk]) (.inl ⟨eW, w.H.S, rfl, by decide, by have := S_le w; simp only [eW]; omega_arith⟩)
      · exact out_apart hp (by omega_using [hk]) (.inl ⟨eT, w.H.D, rfl, by decide, by simp only [eT]; omega_arith⟩)
      · exact (out_apart hp (by omega_using [hk]) (r := stk s₀) (.inr ⟨512, rfl, Nat.le_refl _⟩)).sub_right hb
    have := keep_fr a.frame dO (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
    rw [BitVec.add_zero] at this
    exact this.trans (by rw [hm])
  · have hl : (k0 w prk).length = w.H.B := blockKey_length w prk
    have hou : w.hH.SH.Repr t.mem (key s₀ + BitVec.ofNat 64 192) (xorPad (k0 w prk) opad) :=
      w.hH.congr _ _ _ _ (fun i hi => ER.keyB hp h.er (o := 192) (n := w.H.S)
        (by have := S_le w; omega_using [this]) i hi) hK.2
    have htl : (Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]).length =
        pl w k + infoLen s₀ + 1 := by
      rw [List.length_append, List.length_append, tBlock_len, bytesAt_length]; rfl
    have hplD : pl w k ≤ w.H.D := by unfold pl; split <;> omega_using []
    have := hf (k0 w prk) (Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)])
      hl (by rw [hl, htl]; omega_using [hil, hplD])
      (by rw [hm]; exact hw prk hK) (by rw [u.other _ (by decide), ha.a2, htl]) (by rw [hm]; exact hou)
    exact this

/-- `finalize`'s arguments. -/
theorem argsF_ok {k : Nat} {t : State} (h : BR w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.block finT) t fun u => BR w s₀ k u ∧ FA w s₀ k u ∧
      WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) ∧
      u.syms = s₀.syms := by
  have hD := w.hH.hD64
  have hpl : pl w k ≤ 64 := by unfold pl; split <;> omega_using [hD]
  have hil := info_lt hp
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  unfold finT
  refine (VG.RISCV64.WP.of_syms (wp_addi (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ =>
    wp_add fun t₃ u₃ => wp_add fun t₄ u₄ => wp_addi (by decide) fun t₅ u₅ => wp_addi (by decide) fun t₆ u₆ =>
    WP.block_nil fun sy => ?_))
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₆ : ER w s₀ t₆ := h.er.same (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy
    (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]) m₆
  have g : ∀ r ∈ bregs, t₆.gpr r = t.gpr r := fun r hr => by
    simp only [bregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
  have h₆ : BR w s₀ k t₆ := h.keep k₆ g (by rw [m₆])
  have fa : FA w s₀ k t₆ := ⟨by upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]; rw [h.er.s1],
    by upd_simp [u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]; rw [h.er.s10], ?_,
    by upd_simp [u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]; rw [h.er.s1]⟩
  · exact ⟨h₆, fa, fun prk hK => by rw [m₆]; exact hw prk hK, sy.trans h.er.sy⟩
  · upd_simp [u₆.other, u₅.gpr, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.other, u₁.other]
    rw [h.er.s8, h.s9, h.er.s4]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (s₀.gpr .a2).toNat < 2 ^ 64 := (s₀.gpr .a2).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [hB, hpl] : w.H.B < 2 ^ 64), Nat.mod_eq_of_lt (by omega_using [hpl] : pl w k < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hB, hpl] : w.H.B + pl w k < 2 ^ 64),
      Nat.mod_eq_of_lt (show w.H.B + pl w k + infoLen s₀ < 2 ^ 64 by
        have hplD : pl w k ≤ w.H.D := by unfold pl; split <;> omega_using []
        omega_using [hplD, hil])]
    show (w.H.B + pl w k + infoLen s₀ + 1) % 2 ^ 64 = (w.H.B + (pl w k + infoLen s₀ + 1)) % 2 ^ 64
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

/-- `finalize` through the table. -/
theorem callF_ok {k : Nat} {t : State} (h : BR w s₀ k t) (fa : FA w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (tcall 2 f.fin) t fun u => BR w s₀ k u ∧ TF w s₀ k u ∧ u.syms = s₀.syms := by
  unfold tcall
  refine WP.seq (WP.mono (tload2 hp h.er) fun t' ⟨u, sy'⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (fin_step hp h fa hw u sy')
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy', h.er.sy]; exact hp.tok.f

/-- `finalize`'s arguments, then `finalize` through the table. -/
theorem stageF_ok {k : Nat} {t : State} (h : BR w s₀ k t)
    (hw : WS w s₀ t fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) k ++ infoOf s₀ ++ [BitVec.ofNat 8 (k + 1)]) :
    WP isa (.seq (.block finT) (tcall 2 f.fin)) t fun u => BR w s₀ k u ∧ TF w s₀ k u ∧ u.syms = s₀.syms :=
  WP.seq (WP.mono (argsF_ok hp h hw) fun _ ⟨hb, fa, hw', _⟩ => callF_ok hp hb fa hw')

end

/-! ## The copy to `out` -/

theorem wp_andR {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `min(d, r)`, as `outArgs` computes it. -/
theorem min_sel {d r : Nat} (hd : d < 2 ^ 64) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r + ((BitVec.ofNat 64 d - BitVec.ofNat 64 r) &&&
      (BitVec.ofNat 64 0 - (if BitVec.ofNat 64 d < BitVec.ofNat 64 r then 1 else 0))) =
      BitVec.ofNat 64 (min d r) := by
  have e : (BitVec.ofNat 64 d < BitVec.ofNat 64 r) ↔ d < r := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hr]
  by_cases h : d < r
  · rw [show (if BitVec.ofNat 64 d < BitVec.ofNat 64 r then (1 : BitVec 64) else 0) = 1 by simp only [eq_true (e.mpr h), ↓reduceIte], show BitVec.ofNat 64 0 - (1 : BitVec 64) = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.add_comm, BitVec.sub_add_cancel, Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [show (if BitVec.ofNat 64 d < BitVec.ofNat 64 r then (1 : BitVec 64) else 0) = 0 by simp only [eq_false (fun h' => h (e.mp h')), ↓reduceIte], show BitVec.ofNat 64 0 - (0 : BitVec 64) = 0#64 by decide, BitVec.and_zero,
      BitVec.add_zero, Nat.min_eq_right (by omega_using [h])]

/-- The bytes of `T(k + 1)` block `k + 1` writes to `out`. -/
abbrev nb (w : HVar) (s₀ : State) (k : Nat) : Nat := min w.H.D (outLen s₀ - k * w.H.D)

theorem done_succ {w : HVar} {s₀ : State} {k : Nat} (h : k * w.H.D < outLen s₀) :
    done w s₀ (k + 1) = k * w.H.D + nb w s₀ k := by
  unfold done nb; rw [Nat.succ_mul]; omega_using [h]

/-- The first `n` of `N` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n N : Nat} (h : n ≤ N) :
    bytesAt m p n = (bytesAt m p N).take n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [VG.Proof.Hmac.Common.bytesAt_add, List.take_left' (bytesAt_length _ _ _)]

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- `min(D, rem)` bytes of `T(k + 1)` to `out`, then the registers for block
`k + 2`. -/
theorem out_ok {k : Nat} {t : State} (h : BR w s₀ k t) (hT : TF w s₀ k t) :
    WP isa (.seq (.block outArgs) (.seq (Impl.Words.RISCV64.copyLoop .t1 .a4 .a5 .a6) (.block nextBlock))) t
      fun u => EI w s₀ (k + 1) u ∧ u.syms = s₀.syms := by
  have hfr : eFr = 368 := rfl
  have hD := w.hH.hD64
  have hD0 := w.hH.hD0
  have hk := h.lt
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  have hn0 : 0 < nb w s₀ k := by unfold nb; omega_using [hD0, hk]
  have hnD : nb w s₀ k ≤ w.H.D := Nat.min_le_left _ _
  have hnR : k * w.H.D + nb w s₀ k ≤ outLen s₀ := by unfold nb; omega_using [hk]
  unfold outArgs
  refine WP.seq (VG.RISCV64.WP.of_syms (wp_sub fun t₁ u₁ => wp_sltu fun t₂ u₂ => wp_li (by decide) fun t₃ u₃ =>
    wp_sub fun t₄ u₄ => wp_andR fun t₅ u₅ => wp_add fun t₆ u₆ => wp_addi (by decide) fun t₇ u₇ =>
    wp_mv fun t₈ u₈ => wp_sub fun t₉ u₉ => WP.block_nil fun sy => ?_))
  have m₉ : t₉.mem = t.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₉ : ER w s₀ t₉ := h.er.same (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy
    (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]) m₉
  have a6 : t₉.gpr .a6 = BitVec.ofNat 64 (nb w s₀ k) := by
    upd_simp [u₉.other, u₈.other, u₇.other, u₆.gpr, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other,
      u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.er.s7, h.s5]
    exact min_sel (by omega_using [hD]) (by omega_using [hol])
  have a4 : t₉.gpr .a4 = sA s₀ eT := by
    upd_simp [u₉.other, u₈.other, u₇.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
    rw [h.er.s1]
  have a5 : t₉.gpr .a5 = out s₀ + BitVec.ofNat 64 (k * w.H.D) := by
    upd_simp [u₉.other, u₈.gpr, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
    exact h.s2
  have s5 : t₉.gpr .s5 = BitVec.ofNat 64 (outLen s₀ - k * w.H.D) - BitVec.ofNat 64 (nb w s₀ k) := by
    rw [u₉.gpr, ← a6, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.s5]
    upd_simp [u₉.other, u₈.other, u₇.other]
  have hwT : ∀ i < nb w s₀ k, InRegions (t₉.rd ++ t₉.wr) (t₉.gpr .a4 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [a4, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact in_fr hp k₉.wr (by simp only [eT]; omega_using [hi, hnD, hD, hfr])
  have hwO : ∀ i < nb w s₀ k, InRegions t₉.wr (t₉.gpr .a5 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [a5, BitVec.add_assoc, BitVec.ofNat_add_ofNat, k₉.wr, hp.wr]
    exact ⟨outR s₀, by simp, Offset.contains_base _ (by omega_using [hi, hnR]) (by omega_using [hi, hnR, hol])⟩
  have dTO : Region.Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ ⟨sA s₀ eT, nb w s₀ k⟩ :=
    out_apart hp hnR (.inl ⟨eT, _, rfl, by decide, by simp only [eT]; omega_using [hnD, hD, hfr]⟩)
  have hsep : Mem.Sep (t₉.gpr .a5) (nb w s₀ k) (t₉.gpr .a4) (nb w s₀ k) := by
    rw [a5, a4]; exact Region.Disjoint.sep dTO (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.seq (VG.RISCV64.WP.of_syms (WP.mono (WP.rdwr (copyLoop_adv (tmp := .t1) (src := .a4) (dst := .a5)
    (cnt := .a6) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t₉ hn0
    (by omega_using [hnD, hD]) a6 hwT hwO hsep)) fun u ⟨⟨hc, hf, hkp, ha5⟩, hrd, hwr, hsp⟩ sy' => ?_))
  rw [a5] at hf hc ha5
  rw [a4] at hc
  have ku : ER w s₀ u := k₉.keep hp hrd hwr hsp sy' (fun r hr => hkp.gpr (by revert r; decide)) hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr (.inl (Offset.sub_base _ hnR)))
  unfold nextBlock
  refine VG.RISCV64.WP.of_syms (wp_mv fun v₁ e₁ => wp_mv fun v₂ e₂ => wp_addi (by decide) fun v₃ e₃ =>
    WP.block_nil fun sy'' => ?_)
  have mv : v₃.mem = u.mem := by rw [e₃.mem, e₂.mem, e₁.mem]
  have kv : ER w s₀ v₃ := ku.same (by rw [e₃.rd, e₂.rd, e₁.rd]) (by rw [e₃.wr, e₂.wr, e₁.wr])
    (by rw [e₃.sp, e₂.sp, e₁.sp]) sy''
    (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> upd_simp [e₃.other, e₂.other, e₁.other]) mv
  have dfr : ∀ {R : Region}, R.Disjoint ⟨out s₀ + BitVec.ofNat 64 (k * w.H.D), nb w s₀ k⟩ → R.len ≤ 2 ^ 64 →
      bytesAt v₃.mem R.base R.len = bytesAt t.mem R.base R.len := fun hd hl => by
    rw [mv, ← m₉]
    exact keep_fr hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl
  have hpl : pl w (k + 1) = w.H.D := by simp only [pl, Nat.add_one_ne_zero, ↓reduceIte]
  have hds := done_succ (w := w) (s₀ := s₀) hk
  refine ⟨⟨kv, ?_, ?_, ?_, ?_, fun prk hK => ?_, fun prk hK => ?_⟩, sy''.trans (sy'.trans (sy.trans h.er.sy))⟩
  · rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr, ha5, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hds]
  · rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hkp.gpr (by decide), s5, hds]
    apply BitVec.eq_of_toNat_eq
    have hR : (BitVec.ofNat 64 (outLen s₀ - k * w.H.D)).toNat = outLen s₀ - k * w.H.D := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol])]
    rw [VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hR]; omega_using [hnR]) (by omega_using [hnD, hD]), hR,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hol])]
    omega_using [hnR]
  · rw [e₃.other _ (by decide), e₂.gpr, e₁.other _ (by decide), hkp.gpr (by decide), k₉.s7, hpl]
  · rw [e₃.gpr, e₂.other _ (by decide), e₁.other _ (by decide), hkp.gpr (by decide)]
    upd_simp [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
    rw [h.s0, BitVec.ofNat_add_ofNat]
  · have hbl := Proof.Hkdf.blocks_length w.hH.SH.H prk (infoOf s₀) w.hH.hashLen k
    rw [hds, Proof.Hkdf.blocks_succ, List.take_append, List.take_of_length_le (by omega_using [hbl]),
      hbl, Nat.add_sub_cancel_left, VG.Proof.Hmac.Common.bytesAt_add, ← h.ob prk hK, mv]
    congr 1
    · have d₀ := out_apart hp (o := 0) (n := k * w.H.D) (by omega_using [hk])
        (r := ⟨sA s₀ eT, 0⟩) (.inl ⟨eT, 0, rfl, by decide, by decide⟩)
      have := keep_fr hf (R := ⟨out s₀ + BitVec.ofNat 64 0, k * w.H.D⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hk, hol]) (by omega_using [hnR, hol]))
        (by show k * w.H.D ≤ 2 ^ 64; omega_using [hk, hol])
      simp only [BitVec.add_zero] at this
      rw [this, ← m₉]
    · have hcp : bytesAt u.mem (out s₀ + BitVec.ofNat 64 (k * w.H.D)) (nb w s₀ k) =
          bytesAt t₉.mem (sA s₀ eT) (nb w s₀ k) := by
        simp only [bytesAt]; exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)
      rw [hcp, m₉, bytesAt_take _ _ hnD, hT prk hK]
  · rw [hpl, dfr (R := ⟨sA s₀ eT, w.H.D⟩) (out_apart hp hnR (.inl ⟨eT, w.H.D, rfl, by decide,
      by simp only [eT]; omega_using [hD, hfr]⟩)).symm (by show w.H.D ≤ 2 ^ 64; omega_using [hD])]
    exact hT prk hK

end

/-! ## The blocks -/

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
/-- While bytes of `out` are left, the state before block `k + 1` is one during it. -/
theorem ei_br {k : Nat} {t : State} (h : EI w s₀ k t) (hs : t.gpr .s5 ≠ 0) : BR w s₀ k t ∧ TB w s₀ k t := by
  have hlt : k * w.H.D < outLen s₀ := by
    refine Nat.lt_of_not_le fun hc => hs ?_
    rw [h.s5, show done w s₀ k = outLen s₀ from Nat.min_eq_right hc, Nat.sub_self]; rfl
  have hd : done w s₀ k = k * w.H.D := Nat.min_eq_left (Nat.le_of_lt hlt)
  refine ⟨⟨h.er, by rw [h.s2, hd], by rw [h.s5, hd], h.s9, h.s0, hlt, fun prk hK => ?_⟩, h.tb⟩
  have := h.ob prk hK
  rw [hd] at this
  rw [this, List.take_of_length_le (by
    rw [Proof.Hkdf.blocks_length w.hH.SH.H prk (infoOf s₀) w.hH.hashLen k])]

/-- One block. -/
theorem block_ok {k : Nat} {t : State} (h : EI w s₀ k t) (hs : t.gpr .s5 ≠ 0) :
    WP isa (block f) t fun u => EI w s₀ (k + 1) u ∧ u.syms = s₀.syms := by
  obtain ⟨hb, ht⟩ := ei_br h hs
  unfold block
  refine WP.seq (WP.mono (copy_ok hp hb ht) fun t₁ ⟨b₁, h₁, w₁, _⟩ => ?_)
  refine WP.seq (WP.mono (stageT_ok hp b₁ h₁ w₁) fun t₂ ⟨b₂, h₂, w₂, _⟩ => ?_)
  refine WP.seq (WP.mono (stageI_ok hp b₂ h₂ w₂) fun t₃ ⟨b₃, h₃, w₃, _⟩ => ?_)
  refine WP.seq (WP.mono (stageC_ok hp b₃ h₃ w₃) fun t₄ ⟨b₄, h₄, w₄, _⟩ => ?_)
  refine WP.seq (WP.mono (stageF_ok hp b₄ w₄) fun t₅ ⟨b₅, h₅, _⟩ => ?_)
  exact out_ok hp b₅ h₅

omit hp in
/-- `ofNat x` is not zero for a positive `x` below `2 ^ 64`. -/
theorem ofNat_ne_zero {x : Nat} (h₀ : 0 < x) (h : x < 2 ^ 64) : BitVec.ofNat 64 x ≠ 0 := fun e =>
  absurd (congrArg BitVec.toNat e) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; exact Nat.ne_of_gt h₀)

/-- The blocks, while bytes of `out` are left. -/
theorem loop_ok {k : Nat} {t : State} (h : EI w s₀ k t) (hs : t.gpr .s5 ≠ 0) :
    WP isa (.loop (block f) (.nonzero .s5)) t fun u =>
      ∃ K, EI w s₀ K u ∧ outLen s₀ ≤ K * w.H.D ∧ u.syms = s₀.syms := by
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  have hD0 := w.hH.hD0
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧ EI w s₀ j u ∧ u.gpr .s5 ≠ 0) ?_ _ t ⟨k, rfl, h, hs⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  have hlt := (ei_br hj hu).1.lt
  refine WP.mono (block_ok hp hj hu) fun v ⟨hv, sy⟩ => ?_
  rw [Steps.eval_nonzero_ofNat v .s5 (by omega_using [hol]) hv.s5]
  by_cases e : outLen s₀ ≤ (j + 1) * w.H.D
  · refine .inl ⟨?_, j + 1, hv, e, sy⟩
    rw [show done w s₀ (j + 1) = outLen s₀ from Nat.min_eq_right e, Nat.sub_self]; rfl
  · have hd : done w s₀ (j + 1) = (j + 1) * w.H.D := Nat.min_eq_left (by omega_using [e])
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    refine .inr ⟨?_, outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, e, hD0, hsm], j + 1, rfl, hv, ?_⟩
    · rw [hd, decide_eq_true (by omega_using [e] : outLen s₀ - (j + 1) * w.H.D ≠ 0)]
    · rw [hv.s5, hd]; exact ofNat_ne_zero (by omega_using [e]) (by omega_using [hol])

omit hp in
theorem restorable : Spill.Restorable .s1 restList := by decide

/-- The frame's body. -/
theorem main_ok : WP isa (expandMain f) s₀ fun u => (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧
      u.gpr .ra = s₀.gpr .ra ∧ u.sp = s₀.sp ∧ u.wr = s₀.wr ∧ ∀ prk, Keyd w s₀ prk →
        bytesAt u.mem (out s₀) (outLen s₀) =
          (Spec.Hkdf.blocks w.hH.SH.H prk (infoOf s₀) ((outLen s₀ + w.H.D - 1) / w.H.D) [] 1).take (outLen s₀) := by
  have hfr : eFr = 368 := rfl
  have hol : outLen s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt
  have hD0 := w.hH.hD0
  unfold expandMain
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => ?_)
  have hd0 : done w s₀ 0 = 0 := by simp only [done, Nat.zero_mul, Nat.zero_min]
  have s5 : t₁.gpr .s5 = BitVec.ofNat 64 (outLen s₀) := by rw [h₁.s5, hd0, Nat.sub_zero]
  refine WP.seq (WP.mono (Q := fun (u : State) => ∃ K, EI w s₀ K u ∧ outLen s₀ ≤ K * w.H.D ∧ u.syms = s₀.syms)
    (WP.ite _ (Steps.eval_nonzero_ofNat t₁ .s5 hol s5) (fun ht => ?_) (fun he => ?_)) fun t₂ ⟨K, h₂, hK, _⟩ => ?_)
  · exact loop_ok hp h₁ (by
      rw [s5]; exact ofNat_ne_zero (Nat.pos_of_ne_zero (of_decide_eq_true ht)) hol)
  · refine WP.block_nil ⟨0, h₁, ?_, h₁.er.sy⟩
    rw [Decidable.not_not.mp (of_decide_eq_false he)]; exact Nat.zero_le _
  have k₂ := h₂.er
  refine WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k₂.s1
    (by decide) restorable
    (fun q hq => in_fr hp k₂.wr (by
      simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
    (k₂.saved.sub (by decide))) fun u hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, k₂.sp], by rw [hr.wr, k₂.wr],
      fun prk hk => ?_⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact .inl (by decide) | exact .inr k₂.s11
  · exact hr.gpr_of (.inl (by decide))
  · have hdK : done w s₀ K = outLen s₀ := Nat.min_eq_right hK
    have ob := h₂.ob prk hk
    rw [hdK] at ob
    rw [hr.mem, ob]
    -- Both block counts cover the `L` bytes.
    have hN : outLen s₀ ≤ (outLen s₀ + w.H.D - 1) / w.H.D * w.H.D := by
      have e₁ := Nat.div_add_mod (outLen s₀ + w.H.D - 1) w.H.D
      have e₂ := Nat.mod_lt (outLen s₀ + w.H.D - 1) hD0
      rw [Nat.mul_comm] at e₁
      omega_using [e₁, e₂, hD0]
    have tk := fun a b (ha : outLen s₀ ≤ a * w.H.D) =>
      Proof.Hkdf.blocks_take w.hH.SH.H prk (infoOf s₀) w.hH.hashLen (a := a) ha b
    rcases Nat.le_total K ((outLen s₀ + w.H.D - 1) / w.H.D) with hl | hl
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
      rw [hj, tk K j hK]
    · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hl
      rw [hj, tk _ j hN]

end

/-- `vg_hkdf_expand`, in its frame. -/
theorem expand_correct {w : HVar} {f : Fns} {ns : List String} {s : State}
    (hp : (expandR w f ns eStack).pre s) :
    WP isa (expand f) s fun s' => abiPreserved s s' ∧ (expandR w f ns eStack).post s s' := by
  have hfr : eFr = 368 := rfl
  have hsp : eStack ≤ s.sp.toNat := hp.2.2.2.2.2.2.2.1
  obtain p := pre_alloc hp
  unfold expand
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have : eStack = eFr + 512 := rfl; omega_using [hsp, this])
    (WP.mono (main_ok p) fun v ⟨hcs, hra, hvsp, hvwr, hP⟩ m un fl => ?_)
  refine ⟨⟨fun r hr => hcs r hr, ?_, hra⟩, fun prk hK => ?_⟩
  · show v.sp + BitVec.ofNat 64 eFr = s.sp
    rw [hvsp]; simp only [allocd, BitVec.sub_add_cancel]
  -- The `free` loses the frame's bytes, which lie apart from `out`.
  obtain e : bytesAt m (s.gpr .a3) (s.gpr .a4).toNat = bytesAt v.mem (s.gpr .a3) (s.gpr .a4).toNat :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => lost_byte fl (R := outR (allocd eFr s)) p.f_o.symm hi
  rw [e]
  refine Eq.trans ?_ (congrArg some (hP prk hK)).symm
  have hol : (s.gpr .a4).toNat ≤ 255 * w.H.D := p.ol
  unfold Spec.Hkdf.expand
  rw [ite_eq_right (Nat.not_lt.mpr hol)]
  rfl

/-! ## Constant time -/

/-- The registers that hold public values from the prologue on. -/
abbrev pubRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-- The taint checks of the pieces of `vg_hkdf_expand` between the calls. -/
structure EChecks : Prop where
  pro : Ck [.a0, .a1, .a2, .a3, .a4, .a5] (.block expandPro)
  tl1 : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 1)])
  tl2 : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 2)])
  cp : Ck pubRegs (.seq (.block copyArgs) (Impl.Words.RISCV64.copyAny .t0 .a4 .a5 .a6))
  uT : Ck pubRegs (.block updT)
  uI : Ck pubRegs (.block updI)
  uC : Ck pubRegs (.block updC)
  fT : Ck pubRegs (.block finT)
  ou : Ck pubRegs (.seq (.block outArgs) (.seq (Impl.Words.RISCV64.copyLoop .t1 .a4 .a5 .a6) (.block nextBlock)))
  nil : Ck [] (.block [])
  epi : Ck [.s1] (.block restore)

theorem echecks : EChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : HVar) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5], s₀.gpr r = s₀'.gpr r
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.hfN = s₀'.syms w.hfN

section
variable {w : HVar} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
/-- During the same block, the two runs agree on the public registers. -/
theorem agB {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') :
    t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  have e4 := hq.regs .a4 (by simp)
  refine ⟨by rw [h.er.sp, h'.er.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.s0, h'.s0]
  · rw [h.er.s1, h'.er.s1, hq.sp]
  · rw [h.s2, h'.s2, show out s₀ = out s₀' from hq.regs .a3 (by simp)]
  · rw [h.er.s3, h'.er.s3]; exact hq.regs .a1 (by simp)
  · rw [h.er.s4, h'.er.s4]; exact hq.regs .a2 (by simp)
  · rw [h.s5, h'.s5, show outLen s₀ = outLen s₀' from congrArg BitVec.toNat e4]
  · rw [h.er.s6, h'.er.s6]; exact hq.regs .a5 (by simp)
  · rw [h.er.s7, h'.er.s7]
  · rw [h.er.s8, h'.er.s8]
  · rw [h.s9, h'.s9]
  · rw [h.er.s10, h'.er.s10]; exact hq.regs .a0 (by simp)

omit hp hp' in
theorem ag6 {k : Nat} {t t' : State} (h : BR w s₀ k t) (h' : BR w s₀' k t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.s6], t.gpr r = t'.gpr r :=
  ⟨(agB hq h h').1, fun r hr => (agB hq h h').2 r (by simp at hr; subst hr; simp)⟩

omit hp hp' in
/-- Before the same block, the two runs have as many bytes of `out` left. -/
theorem s5E {k : Nat} {t t' : State} (h : EI w s₀ k t) (h' : EI w s₀' k t') : t.gpr .s5 = t'.gpr .s5 := by
  rw [h.s5, h'.s5]
  show BitVec.ofNat 64 ((s₀.gpr .a4).toNat - min (k * w.H.D) (s₀.gpr .a4).toNat) =
    BitVec.ofNat 64 ((s₀'.gpr .a4).toNat - min (k * w.H.D) (s₀'.gpr .a4).toNat)
  rw [hq.regs .a4 (by simp)]

/-- One block leaks the same trace in both runs. -/
theorem block_rel (j : Nat) :
    RelCT isa (fun t t' => (EI w s₀ j t ∧ t.gpr .s5 ≠ 0) ∧ (EI w s₀' j t' ∧ t'.gpr .s5 ≠ 0)) (block f)
      fun u u' => (EI w s₀ (j + 1) u ∧ u.syms = s₀.syms) ∧ (EI w s₀' (j + 1) u' ∧ u'.syms = s₀'.syms) := by
  have kc := echecks
  have e0 := hq.regs .a0 (by simp); have e1 := hq.regs .a1 (by simp); have e2 := hq.regs .a2 (by simp)
  have esp := hq.sp
  have il : infoLen s₀ = infoLen s₀' := congrArg BitVec.toNat e2
  unfold block
  have r1 := rel_agree (P₁ := fun t => EI w s₀ j t ∧ t.gpr .s5 ≠ 0) (P₂ := fun t => EI w s₀' j t ∧ t.gpr .s5 ≠ 0)
    (G₁ := fun u => BR w s₀ j u ∧ TB w s₀ j u ∧ WS w s₀ u (fun _ => []) ∧ u.syms = s₀.syms)
    (G₂ := fun u => BR w s₀' j u ∧ TB w s₀' j u ∧ WS w s₀' u (fun _ => []) ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq (ei_br h.1 h.2).1 (ei_br h'.1 h'.2).1) kc.cp
    (fun t h => copy_ok hp (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
    (fun t h => copy_ok hp' (ei_br h.1 h.2).1 (ei_br h.1 h.2).2)
  have r2 := rel_agree (P₁ := fun u => BR w s₀ j u ∧ TB w s₀ j u ∧ WS w s₀ u (fun _ => []) ∧ u.syms = s₀.syms)
    (P₂ := fun u => BR w s₀' j u ∧ TB w s₀' j u ∧ WS w s₀' u (fun _ => []) ∧ u.syms = s₀'.syms)
    (G₁ := AT w s₀ j (sA s₀ eT) (pl w j) 0 fun _ => []) (G₂ := AT w s₀' j (sA s₀' eT) (pl w j) 0 fun _ => [])
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uT
    (fun t h => argsT_ok hp h.1 h.2.1 h.2.2.1) (fun t h => argsT_ok hp' h.1 h.2.1 h.2.2.1)
  have r3 : RelCT isa (fun t t' => AT w s₀ j (sA s₀ eT) (pl w j) 0 (fun _ => []) t ∧
      AT w s₀' j (sA s₀' eT) (pl w j) 0 (fun _ => []) t') (tcall 1 f.upd)
      fun u u' => PT w s₀ j u ∧ PT w s₀' j u' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag6 hq a.br a'.br)
      (fun t a => tload1 hp a.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.br.er)
      (fun t a => by rw [a.sy]; exact hp.tok.u) (fun t a => by rw [a.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, v, _⟩, ⟨t', a', v', _⟩⟩ => ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.sp, v'.sp, a.br.er.sp, a'.br.er.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.a1, a'.a1]⟩))
      (fun t a => callT_ok hp a) (fun t a => callT_ok hp' a)
  have r4 := rel_agree (P₁ := PT w s₀ j) (P₂ := PT w s₀' j)
    (G₁ := AT w s₀ j (info s₀) (infoLen s₀) (pl w j) fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) j)
    (G₂ := AT w s₀' j (info s₀') (infoLen s₀') (pl w j) fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀') j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uI
    (fun t h => argsI_ok hp h.1 h.2.1 h.2.2.1) (fun t h => argsI_ok hp' h.1 h.2.1 h.2.2.1)
  have r5 : RelCT isa (fun t t' =>
      AT w s₀ j (info s₀) (infoLen s₀) (pl w j) (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) j) t ∧
      AT w s₀' j (info s₀') (infoLen s₀') (pl w j) (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀') j) t')
      (tcall 1 f.upd) fun u u' => PI w s₀ j u ∧ PI w s₀' j u' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag6 hq a.br a'.br)
      (fun t a => tload1 hp a.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.br.er)
      (fun t a => by rw [a.sy]; exact hp.tok.u) (fun t a => by rw [a.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, v, _⟩, ⟨t', a', v', _⟩⟩ => ⟨upd_args hp a.br a.ua v,
        by have := upd_args hp' a'.br a'.ua v'; simp only [sA, info, infoLen] at this ⊢; rwa [← esp, ← e1, ← e2] at this,
        by rw [v.sp, v'.sp, a.br.er.sp, a'.br.er.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.a1, a'.a1]⟩))
      (fun t a => callI_ok hp a) (fun t a => callI_ok hp' a)
  have r6 := rel_agree (P₁ := PI w s₀ j) (P₂ := PI w s₀' j) (G₁ := AC w s₀ j) (G₂ := AC w s₀' j)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.uC
    (fun t h => argsC_ok hp h.1 h.2.1 h.2.2.1) (fun t h => argsC_ok hp' h.1 h.2.1 h.2.2.1)
  have r7 : RelCT isa (fun t t' => AC w s₀ j t ∧ AC w s₀' j t') (tcall 1 f.upd)
      fun u u' => PC w s₀ j u ∧ PC w s₀' j u' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' a a' => ag6 hq a.1.br a'.1.br)
      (fun t a => tload1 hp a.1.br.er) (fun t a => by rw [hq.up]; exact tload1 hp' a.1.br.er)
      (fun t a => by rw [a.1.sy]; exact hp.tok.u) (fun t a => by rw [a.1.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, a, v, _⟩, ⟨t', a', v', _⟩⟩ => ⟨upd_args hp a.1.br a.1.ua v,
        by have := upd_args hp' a'.1.br a'.1.ua v'; simp only [sA] at this ⊢; rwa [← esp] at this,
        by rw [v.sp, v'.sp, a.1.br.er.sp, a'.1.br.er.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.1.a1, a'.1.a1, il]⟩))
      (fun t a => callC_ok hp a) (fun t a => callC_ok hp' a)
  have r8 := rel_agree (P₁ := PC w s₀ j) (P₂ := PC w s₀' j)
    (G₁ := fun u => BR w s₀ j u ∧ FA w s₀ j u ∧ WS w s₀ u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) j ++
      infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)]) ∧ u.syms = s₀.syms)
    (G₂ := fun u => BR w s₀' j u ∧ FA w s₀' j u ∧ WS w s₀' u (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀') j ++
      infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]) ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.fT
    (fun t h => argsF_ok hp h.1 h.2.2.1) (fun t h => argsF_ok hp' h.1 h.2.2.1)
  have r9 : RelCT isa (fun t t' =>
      (BR w s₀ j t ∧ FA w s₀ j t ∧ WS w s₀ t (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀) j ++
        infoOf s₀ ++ [BitVec.ofNat 8 (j + 1)]) ∧ t.syms = s₀.syms) ∧
      (BR w s₀' j t' ∧ FA w s₀' j t' ∧ WS w s₀' t' (fun prk => Proof.Hkdf.tBlock w.hH.SH.H prk (infoOf s₀') j ++
        infoOf s₀' ++ [BitVec.ofNat 8 (j + 1)]) ∧ t'.syms = s₀'.syms)) (tcall 2 f.fin)
      fun u u' => (BR w s₀ j u ∧ TF w s₀ j u ∧ u.syms = s₀.syms) ∧ (BR w s₀' j u' ∧ TF w s₀' j u' ∧ u'.syms = s₀'.syms) :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.hfN) kc.tl2 (fun t t' a a' => ag6 hq a.1 a'.1)
      (fun t a => tload2 hp a.1.er) (fun t a => by rw [hq.hf]; exact tload2 hp' a.1.er)
      (fun t a => by rw [a.2.2.2]; exact hp.tok.f) (fun t a => by rw [a.2.2.2, hq.hf]; exact hp'.tok.f)
      (hf_rel fun u u' ⟨⟨t, a, v, _⟩, ⟨t', a', v', _⟩⟩ => ⟨fin_args hp a.1 a.2.1 v,
        by have := fin_args hp' a'.1 a'.2.1 v'; simp only [sA, key] at this ⊢; rwa [← esp, ← e0] at this,
        by rw [v.sp, v'.sp, a.1.er.sp, a'.1.er.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), a.2.1.a2, a'.2.1.a2, il]⟩))
      (fun t a => callF_ok hp a.1 a.2.1 a.2.2.1) (fun t a => callF_ok hp' a.1 a.2.1 a.2.2.1)
  have r10 := rel_agree (P₁ := fun u => BR w s₀ j u ∧ TF w s₀ j u ∧ u.syms = s₀.syms)
    (P₂ := fun u => BR w s₀' j u ∧ TF w s₀' j u ∧ u.syms = s₀'.syms)
    (G₁ := fun u => EI w s₀ (j + 1) u ∧ u.syms = s₀.syms) (G₂ := fun u => EI w s₀' (j + 1) u ∧ u.syms = s₀'.syms)
    (rs := pubRegs) (fun t t' h h' => agB hq h.1 h'.1) kc.ou
    (fun t h => out_ok hp h.1 h.2.1) (fun t h => out_ok hp' h.1 h.2.1)
  exact r1.seq ((r2.seq r3).seq ((r4.seq r5).seq ((r6.seq r7).seq ((r8.seq r9).seq r10))))

/-- The blocks leak the same trace in both runs. -/
theorem loop_rel {k : Nat} :
    RelCT isa (fun t t' => (EI w s₀ k t ∧ t.gpr .s5 ≠ 0) ∧ (EI w s₀' k t' ∧ t'.gpr .s5 ≠ 0))
      (.loop (block f) (.nonzero .s5)) fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
  have hD0 := w.hH.hD0
  refine (RelCT.loop (M := isa) (I := fun n (t t' : State) => ∃ j, n = outLen s₀ - j * w.H.D ∧
      ((EI w s₀ j t ∧ t.gpr .s5 ≠ 0) ∧ (EI w s₀' j t' ∧ t'.gpr .s5 ≠ 0))) (fun n => ?_) (outLen s₀ - k * w.H.D)).mono
    (fun t t' h => ⟨k, rfl, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hn : n = outLen s₀ - j * w.H.D
  · subst hn
    refine (block_rel hp hp' hq j).mono (fun t t' h => h.2) fun u u' ⟨⟨hv, _⟩, ⟨hv', _⟩⟩ => ?_
    have e := s5E hq hv hv'
    refine ⟨by rw [Steps.eval_nonzero, Steps.eval_nonzero, e], fun _ => ⟨⟨_, hv⟩, ⟨_, hv'⟩⟩, fun hc => ?_⟩
    have hs : u.gpr .s5 ≠ 0 := by rw [Steps.eval_nonzero] at hc; simpa using hc
    have hlt := (ei_br hv hs).1.lt
    have hsm : (j + 1) * w.H.D = j * w.H.D + w.H.D := Nat.succ_mul _ _
    exact ⟨outLen s₀ - (j + 1) * w.H.D, by omega_using [hlt, hsm, hD0], j + 1, rfl, ⟨hv, hs⟩, ⟨hv', e ▸ hs⟩⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (expandMain f) fun _ _ => True := by
  have kc := echecks
  have esp := hq.sp
  unfold expandMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := EI w s₀ 0) (G₂ := EI w s₀' 0)
    (rs := [.a0, .a1, .a2, .a3, .a4, .a5]) (fun s s' hs hs' => by subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => EI w s₀ 0 t ∧ EI w s₀' 0 t')
      (.ite (.nonzero .s5) (.loop (block f) (.nonzero .s5)) (.block []))
      fun u u' => (∃ K, EI w s₀ K u) ∧ (∃ K, EI w s₀' K u') := by
    refine RelCT.ite (fun t t' h => by rw [Steps.eval_nonzero, Steps.eval_nonzero, s5E hq h.1 h.2]) ?_ ?_
    · refine (loop_rel hp hp' hq (k := 0)).mono (fun t t' h => ?_) fun _ _ h => h
      obtain ⟨⟨h₁, h₂⟩, hc⟩ := h
      have hs : t.gpr .s5 ≠ 0 := by rw [Steps.eval_nonzero] at hc; simpa using hc
      exact ⟨⟨h₁, hs⟩, ⟨h₂, s5E hq h₁ h₂ ▸ hs⟩⟩
    · exact (rel_agree (P₁ := EI w s₀ 0) (P₂ := EI w s₀' 0) (G₁ := fun u => ∃ K, EI w s₀ K u)
        (G₂ := fun u => ∃ K, EI w s₀' K u) (rs := []) (fun t t' h h' => ⟨by rw [h.er.sp, h'.er.sp, esp], by simp⟩)
        kc.nil (fun t h => WP.block_nil ⟨0, h⟩) (fun t h => WP.block_nil ⟨0, h⟩)).mono (fun t t' h => h.1)
        fun _ _ h => h
  have hfr : eFr = 368 := rfl
  have r3 := rel_agree (P₁ := fun u => ∃ K, EI w s₀ K u) (P₂ := fun u => ∃ K, EI w s₀' K u)
    (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [.s1])
    (fun t t' ⟨_, k⟩ ⟨_, k'⟩ => ⟨by rw [k.er.sp, k'.er.sp, esp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [k.er.s1, k'.er.s1, esp]⟩) kc.epi
    (fun t ⟨_, k⟩ => WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k.er.s1
        (by decide) restorable
        (fun q hq => in_fr hp k.er.wr (by
          simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
        (k.er.saved.sub (by decide))) fun _ _ => trivial)
    (fun t ⟨_, k⟩ => WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp'.al]) k.er.s1
        (by decide) restorable
        (fun q hq => in_fr hp' k.er.wr (by
          simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
        (k.er.saved.sub (by decide))) fun _ _ => trivial)
  exact (r1.seq (r2.seq r3)).mono (fun _ _ h => h) fun _ _ _ => trivial

end

/-- `vg_hkdf_expand` is constant time: two runs whose public data agree
leak the same trace. -/
theorem expand_ct {w : HVar} {f : Fns} {ns : List String} (hns : ∀ n ∈ [w.H.updN, w.hfN], n ∈ ns) :
    ConstantTime isa (expandR w f ns eStack).pre (expandR w f ns eStack).pub (expand f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, qn⟩ := hpub
  have hq : PubEq w (allocd eFr e) (allocd eFr e') :=
    ⟨by simp only [allocd, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3, q4, q5], qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (expand f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold expand
  refine rel_alloc ((main_rel hp hp' hq).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.RISCV64.Expand
