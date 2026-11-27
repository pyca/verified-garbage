module

public import VerifiedGarbage.Proof.Hkdf.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Hkdf.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# HKDF on RISC-V: `vg_hkdf_extract`, correct

The contract the proof is written against (`extractR`), for the table
`hmac` of one hash function `w` (`HVar`), whose functions an indirect call
of `f`'s reaches: `extract(salt, salt_len, ikm, ikm_len, prk, prk_len,
hmac)` writes `HMAC(salt, IKM)` to `prk`, which is `D` bytes long. In its
frame (`xFr` bytes: the save area, then HMAC's inner and outer states), the
prologue saves our caller's registers, keeps the arguments it needs after
the calls in callee-saved registers and loads `D` and `B` from the table
(`pro_ok`, from which on `XR` holds); then `init` with the salt as the key,
`update` with the input keying material and `finalize` into `prk`, each
through the table (`init_ok`, `upd_ok`, `fin_ok`); and the epilogue
restores our caller's registers.
-/

@[expose] public section

namespace VG.Proof.Hkdf.RISCV64.Extract

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_add wp_addSp wp_ld wp_sd)
open VG.Impl.Hkdf.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns tcall)
open VG.Proof.HmacTable.RISCV64 (HVar TabOK TabMem)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

/-- `extract(salt, salt_len, ikm, ikm_len, prk, prk_len, hmac)`, with `N`
bytes of stack, for the table `hmac` of `w`, whose functions an indirect call
of `f`'s reaches, with the addresses of the functions `ns` public. -/
def extractR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let salt : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ikm : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let prk : Region := ⟨s.gpr .a4, w.H.D⟩
    let tab : Region := ⟨s.gpr .a6, 48⟩
    let stk : Region := below s.sp N
    s.rd = [salt, ikm, tab] ∧ s.wr = [prk] ∧ (s.gpr .a5).toNat = w.H.D ∧
      salt.Disjoint prk ∧ ikm.Disjoint prk ∧ tab.Disjoint prk ∧
      s.sp.toNat % 16 = 0 ∧ N ≤ s.sp.toNat ∧
      stk.Disjoint salt ∧ stk.Disjoint ikm ∧ stk.Disjoint prk ∧ stk.Disjoint tab ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + w.H.D ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      TabMem w s.syms (s.gpr .a6) s.mem ∧
      s.mem.readW (s.gpr .a6 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
      s.mem.readW (s.gpr .a6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B ∧ TabOK w f s.syms
  post s s' := bytesAt s'.mem (s.gpr .a4) w.H.D =
    Spec.Hkdf.extract w.hH.SH.H (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
      (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- The stack `vg_hkdf_extract` uses: its frame, and below it what HMAC's
functions use. -/
def xStack : Nat := xFr + 512

section
variable (s₀ : State)

/-- The arguments, on entry to the frame's body. -/
abbrev salt : Addr := s₀.gpr .a0
abbrev saltLen : Nat := (s₀.gpr .a1).toNat
abbrev ikm : Addr := s₀.gpr .a2
abbrev ikmLen : Nat := (s₀.gpr .a3).toNat
abbrev prk : Addr := s₀.gpr .a4
abbrev tab : Addr := s₀.gpr .a6

/-- An address in the frame. -/
abbrev sA (o : Nat) : Addr := s₀.sp + BitVec.ofNat 64 o

abbrev frR : Region := ⟨s₀.sp, xFr⟩
abbrev saltR : Region := ⟨salt s₀, saltLen s₀⟩
abbrev ikmR : Region := ⟨ikm s₀, ikmLen s₀⟩
abbrev tabR : Region := ⟨tab s₀, 48⟩
abbrev stk : Region := below s₀.sp 512

end

/-- The regions the frame's body writes. -/
abbrev prkR (w : HVar) (s₀ : State) : Region := ⟨prk s₀, w.H.D⟩
abbrev wrs (w : HVar) (s₀ : State) : List Region := [frR s₀, prkR w s₀, stk s₀]

/-- The state the frame's body starts in. -/
structure Pre (w : HVar) (f : Fns) (s₀ : State) : Prop where
  rd : s₀.rd = [saltR s₀, ikmR s₀, tabR s₀]
  wr : s₀.wr = [frR s₀, prkR w s₀]
  pl : (s₀.gpr .a5).toNat = w.H.D
  s_p : (saltR s₀).Disjoint (prkR w s₀)
  i_p : (ikmR s₀).Disjoint (prkR w s₀)
  t_p : (tabR s₀).Disjoint (prkR w s₀)
  f_s : (frR s₀).Disjoint (saltR s₀)
  f_i : (frR s₀).Disjoint (ikmR s₀)
  f_p : (frR s₀).Disjoint (prkR w s₀)
  f_t : (frR s₀).Disjoint (tabR s₀)
  b_s : (stk s₀).Disjoint (saltR s₀)
  b_i : (stk s₀).Disjoint (ikmR s₀)
  b_p : (stk s₀).Disjoint (prkR w s₀)
  b_t : (stk s₀).Disjoint (tabR s₀)
  b_f : (stk s₀).Disjoint (frR s₀)
  al : s₀.sp.toNat % 16 = 0
  sp : 512 ≤ s₀.sp.toNat
  top : s₀.sp.toNat + xFr ≤ 2 ^ 64
  ns : (salt s₀).toNat + saltLen s₀ ≤ 2 ^ 64
  ni : (ikm s₀).toNat + ikmLen s₀ ≤ 2 ^ 64
  np : (prk s₀).toNat + w.H.D ≤ 2 ^ 64
  nt : (tab s₀).toNat + 48 ≤ 2 ^ 64
  ta : (tab s₀).toNat % 8 = 0
  tmem : TabMem w s₀.syms (tab s₀) s₀.mem
  tD : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D
  tB : s₀.mem.readW (tab s₀ + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.B
  tok : TabOK w f s₀.syms

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- The state the frame's body starts in, from the contract's precondition. -/
theorem pre_alloc {s : State} (hp : (extractR w f ns xStack).pre s) : Pre w f (allocd xFr s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := hp
  have hfr : xFr = 480 := rfl
  have hN : xStack = xFr + 512 := rfl
  obtain hspN : (s.sp - BitVec.ofNat 64 xFr).toNat = s.sp.toNat - xFr :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by rw [hN] at h8; omega_using [h8]) (by omega_using [hfr])
  obtain subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 xFr, xFr⟩ (below s.sp xStack) :=
    Offset.sub_below s.sp (by rw [hN]; omega_using []) (by rw [hN]; omega_using [])
  obtain subS : Region.Sub (below (s.sp - BitVec.ofNat 64 xFr) 512) (below s.sp xStack) := by
    have := below_body' s.sp xFr 512
    rwa [Nat.add_comm 512, ← hN] at this
  refine ⟨h1, by show (⟨s.sp - BitVec.ofNat 64 xFr, xFr⟩ : Region) :: s.wr = _; rw [h2]; rfl, h3, h4, h5, h6,
    h9.sub_left subF, h10.sub_left subF, h11.sub_left subF, h12.sub_left subF,
    h9.sub_left subS, h10.sub_left subS, h11.sub_left subS, h12.sub_left subS, ?_, ?_, ?_, ?_,
    h13, h14, h15, h16, h17, h18, h19, h20, h21⟩
  · show (below (s.sp - BitVec.ofNat 64 xFr) 512).Disjoint ⟨s.sp - BitVec.ofNat 64 xFr, xFr⟩
    exact (Offset.base_disjoint_below _ (by have := s.sp.isLt; rw [hN] at h8; omega_arith)).symm
  · show (s.sp - BitVec.ofNat 64 xFr).toNat % 16 = 0
    rw [hspN]; omega_using [hfr, h7]
  · show 512 ≤ (s.sp - BitVec.ofNat 64 xFr).toNat
    rw [hspN]; rw [hN] at h8; omega_using [h8]
  · show (s.sp - BitVec.ofNat 64 xFr).toNat + xFr ≤ 2 ^ 64
    rw [hspN]; have := s.sp.isLt; rw [hN] at h8; omega_using [hfr]

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the end of the prologue on. -/
structure XR (w : HVar) (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  sy : t.syms = s₀.syms
  s1 : t.gpr .s1 = s₀.sp
  s2 : t.gpr .s2 = prk s₀
  s3 : t.gpr .s3 = ikm s₀
  s4 : t.gpr .s4 = s₀.gpr .a3
  s6 : t.gpr .s6 = tab s₀
  s7 : t.gpr .s7 = BitVec.ofNat 64 w.H.D
  s8 : t.gpr .s8 = BitVec.ofNat 64 w.H.B
  s11 : t.gpr .s11 = s₀.gpr .s11
  saved : Spill.Saved s₀.sp s₀.gpr saved t.mem
  frame : Frame (wrs w s₀) s₀.mem t.mem

/-- The registers `XR` fixes. -/
abbrev kregs : List Reg := [.s1, .s2, .s3, .s4, .s6, .s7, .s8, .s11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_in : ∀ q ∈ saved, 0 ≤ q.2 ∧ q.2 + 8 ≤ 0 + 96 := by
  intro q hq
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A part of the frame after the save area, `prk`, or the stack below the
frame. -/
def Wk (w : HVar) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = ⟨sA s₀ o, n⟩ ∧ 96 ≤ o ∧ o + n ≤ xFr) ∨ Region.Sub r (prkR w s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ 512

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

theorem Wk.ok {r : Region} (h : Wk w s₀ r) :
    Region.Disjoint ⟨s₀.sp + BitVec.ofNat 64 0, 96⟩ r ∧ ∃ r' ∈ wrs w s₀, Region.Sub r r' := by
  have hfr : xFr = 480 := rfl
  have sv : Region.Sub ⟨s₀.sp + BitVec.ofNat 64 0, 96⟩ (frR s₀) := Offset.sub_base _ (by omega_using [hfr])
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨Offset.disjoint _ (.inl (by omega_using [h₁])) (by decide) (by omega_using [h₂, hfr]),
      _, by simp, Offset.sub_base _ h₂⟩
  · exact ⟨(hp.f_p.sub_left sv).sub_right h, _, by simp, h⟩
  · have hb : Region.Sub (below s₀.sp n) (stk s₀) := Offset.below_mono _ hn (by decide)
    exact ⟨(hp.b_f.symm.sub_left sv).sub_right hb, _, by simp, hb⟩

theorem XR.keep {t t' : State} (h : XR w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hw : ∀ r ∈ rs, Wk w s₀ r) : XR w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s2, (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4,
    (hg _ (by simp)).trans h.s6, (hg _ (by simp)).trans h.s7, (hg _ (by simp)).trans h.s8,
    (hg _ (by simp)).trans h.s11,
    h.saved.frame_in saved_in hf fun r hr => (Wk.ok hp (hw r hr)).1,
    h.frame.trans (hf.sub fun r hr => (Wk.ok hp (hw r hr)).2)⟩

omit hp in
theorem XR.same {t t' : State} (h : XR w s₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hsy : t'.syms = t.syms) (hg : ∀ r ∈ kregs, t'.gpr r = t.gpr r) (hm : t'.mem = t.mem) : XR w s₀ t' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, hsy.trans h.sy, (hg _ (by simp)).trans h.s1,
    (hg _ (by simp)).trans h.s2, (hg _ (by simp)).trans h.s3, (hg _ (by simp)).trans h.s4,
    (hg _ (by simp)).trans h.s6, (hg _ (by simp)).trans h.s7, (hg _ (by simp)).trans h.s8,
    (hg _ (by simp)).trans h.s11, by rw [hm]; exact h.saved, by rw [hm]; exact h.frame⟩

omit hp in
open VG.RISCV64.Steps (Upd) in
theorem XR.upd {t t' : State} (h : XR w s₀ t) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd t t' d v) (hsy : t'.syms = t.syms) : XR w s₀ t' := by
  have g : ∀ r ∈ kregs, t'.gpr r = t.gpr r := fun r hr => u.other r fun e => hd (e ▸ hr)
  exact ⟨u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp, hsy.trans h.sy,
    (g _ (by simp)).trans h.s1, (g _ (by simp)).trans h.s2, (g _ (by simp)).trans h.s3, (g _ (by simp)).trans h.s4,
    (g _ (by simp)).trans h.s6, (g _ (by simp)).trans h.s7, (g _ (by simp)).trans h.s8,
    (g _ (by simp)).trans h.s11, by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.frame⟩

/-- A part of the frame after the save area is in the writable regions. -/
theorem in_fr {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) :
    InRegions (t.rd ++ t.wr) (sA s₀ o) n :=
  ⟨_, List.mem_append_right _ (by rw [hwr, hp.wr]; exact List.mem_cons_self),
    Offset.contains_base _ h (by have : xFr = 480 := rfl; omega_using [h, this])⟩

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem XR.bytes {t : State} (hk : XR w s₀ t) {p : Addr} {n : Nat}
    (hd : ∀ r ∈ wrs w s₀, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt s₀.mem p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hk.frame.bytes (R := ⟨p, n⟩) hd hn hi

theorem XR.saltB {t : State} (hk : XR w s₀ t) : bytesAt t.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_s.symm
    · exact hp.s_p
    · exact hp.b_s.symm) (Nat.le_of_lt (s₀.gpr .a1).isLt)

theorem XR.ikmB {t : State} (hk : XR w s₀ t) : bytesAt t.mem (ikm s₀) (ikmLen s₀) = bytesAt s₀.mem (ikm s₀) (ikmLen s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.f_i.symm
    · exact hp.i_p
    · exact hp.b_i.symm) (Nat.le_of_lt (s₀.gpr .a3).isLt)

/-- A word of the table is as on entry. -/
theorem XR.tabW {t : State} (hk : XR w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
    t.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 :=
  hk.frame.readW (r := tabR s₀) (Offset.contains_base _ ho (by have := hp.nt; omega_using [ho]))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.f_t.symm
      · exact hp.t_p
      · exact hp.b_t.symm) (by decide)

/-- The table's word `j`, readable and aligned. -/
theorem tin {t : State} (hk : XR w s₀ t) {o : Nat} (ho : o + 8 ≤ 48) :
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

/-! ## The prologue -/

theorem pro_eq : extractPro = .addSp .t0 0 :: (Spill.saveCode .t0 saved ++
    [mov .s1 .t0, mov .s3 .a2, mov .s4 .a3, mov .s2 .a4, mov .s6 .a6, .load .d .s7 .s6 32, .load .d .s8 .s6 40,
      mov .a2 .a0, mov .a3 .a1, .addi .a0 .s1 xIn, .addi .a1 .s1 xOut]) := rfl

/-- After the prologue: `XR`, and `init`'s arguments. -/
def XA (w : HVar) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ t.gpr .a0 = sA s₀ xIn ∧ t.gpr .a1 = sA s₀ xOut ∧ t.gpr .a2 = salt s₀ ∧ t.gpr .a3 = s₀.gpr .a1

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- A part of the frame is in the writable regions. -/
theorem in_frw {t : State} (hwr : t.wr = s₀.wr) {o n : Nat} (h : o + n ≤ xFr) : InRegions t.wr (sA s₀ o) n :=
  ⟨_, by rw [hwr, hp.wr]; exact List.mem_cons_self,
    Offset.contains_base _ h (by have : xFr = 480 := rfl; omega_using [h, this])⟩

theorem pro_ok : WP isa (.block extractPro) s₀ (XA w s₀) := by
  rw [pro_eq]
  have hfr : xFr = 480 := rfl
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
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => ?_
  obtain a6 : s₆.gpr .s6 = tab s₀ := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide), u₂.other _ (by decide)]; exact e₁ _ (by decide)
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr
  obtain mm : s₆.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr saved = _
    rw [t0]
  obtain F₆ : Frame [⟨s₀.sp, 96⟩] s₀.mem s₆.mem := by
    rw [mm, hm₁]
    exact Spill.saveMem_frame_base (n := 96) (fun p hp' => (saved_in p hp').2) (by omega_using []) _ _ _
  obtain hrw : ∀ o, o + 8 ≤ 48 → s₆.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 =
      s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 := fun o ho =>
    F₆.readW (r := tabR s₀) (Offset.contains_base _ ho (by have := hp.nt; omega_using [ho])) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.f_t.symm.sub_right (Region.sub_prefix (by omega_using [hfr]))) (by decide)
  obtain hin : ∀ o, o + 8 ≤ 48 → ∀ s : State, s.rd = s₀.rd → InRegions (s.rd ++ s.wr) (tab s₀ + BitVec.ofNat 64 o) 8 :=
    fun o ho s hrd => ⟨tabR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp),
      Offset.contains_base _ ho (by have := hp.nt; omega_using [ho])⟩
  refine wp_ld (by decide) (by rw [a6]) (tal hp (o := 32) (by decide) (by decide)) (hin 32 (by decide) _ rd₆)
    fun s₇ u₇ => wp_ld (by decide) (by rw [u₇.other _ (by decide), a6]) (tal hp (o := 40) (by decide) (by decide))
      (hin 40 (by decide) s₇ (by rw [u₇.rd, rd₆])) fun s₈ u₈ => ?_
  refine wp_mv fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => wp_addi (by decide) fun s₁₁ u₁₁ =>
    wp_addi (by decide) fun s₁₂ u₁₂ => WP.block_nil fun sy => ?_
  obtain m₁₂ : s₁₂.mem = s₆.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain sv : Spill.Saved s₀.sp s₀.gpr saved s₁₂.mem := by
    rw [m₁₂, mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  refine ⟨⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd]; exact rd₆,
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr]; exact wr₆,
    by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp,
    sy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sv, ?_⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    rw [hrw 32 (by decide)]; exact hp.tD
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
    rw [u₇.mem, hrw 40 (by decide)]; exact hp.tB
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · rw [m₁₂]
    exact F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨frR s₀, by simp, Region.sub_prefix (by omega_using [hfr])⟩
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]
  · upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, e₁, t0]

end

/-! ## The calls -/

/-- HMAC's key, its block size. -/
theorem blockKey_length (w : HVar) (k : List Byte) : (blockKey w.hH.SH.H k).length = w.H.B := by
  have hB := w.hH.hB
  have hDB : w.H.D ≤ w.H.B := by have := w.hH.hD64; rcases w.hH.hB64 with h | h <;> omega_using [this, h]
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [w.hH.hashLen]; omega_using [hDB]
  · omega_arith

/-- The key `K₀` the salt makes. -/
abbrev k0Of (w : HVar) (s₀ : State) : List Byte := blockKey w.hH.SH.H (bytesAt s₀.mem (salt s₀) (saltLen s₀))

/-- The input keying material. -/
abbrev ikmOf (s₀ : State) : List Byte := bytesAt s₀.mem (ikm s₀) (ikmLen s₀)

/-- After `init`: the states of `K₀`. -/
def XI (w : HVar) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ w.hH.SH.Repr t.mem (sA s₀ xIn) (xorPad (k0Of w s₀) ipad) ∧
    w.hH.SH.Repr t.mem (sA s₀ xOut) (xorPad (k0Of w s₀) opad)

/-- After `update`'s arguments. -/
def XUA (w : HVar) (s₀ t : State) : Prop :=
  XI w s₀ t ∧ t.gpr .a0 = sA s₀ xIn ∧ t.gpr .a1 = BitVec.ofNat 64 w.H.B ∧ t.gpr .a2 = ikm s₀ ∧
    t.gpr .a3 = s₀.gpr .a3

/-- After `update`: the inner state holds the input keying material too. -/
def XU (w : HVar) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ w.hH.SH.Repr t.mem (sA s₀ xIn) (xorPad (k0Of w s₀) ipad ++ ikmOf s₀) ∧
    w.hH.SH.Repr t.mem (sA s₀ xOut) (xorPad (k0Of w s₀) opad)

/-- After `finalize`'s arguments. -/
def XFA (w : HVar) (s₀ t : State) : Prop :=
  XU w s₀ t ∧ t.gpr .a0 = sA s₀ xIn ∧ t.gpr .a1 = sA s₀ xOut ∧
    t.gpr .a2 = BitVec.ofNat 64 w.H.B + s₀.gpr .a3 ∧ t.gpr .a3 = prk s₀

/-- After `finalize`: `PRK`. -/
def XF (w : HVar) (s₀ t : State) : Prop :=
  XR w s₀ t ∧ bytesAt t.mem (prk s₀) w.H.D = hmacBlockKey w.hH.SH.H (k0Of w s₀) (ikmOf s₀)

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
/-- The states' regions, within the frame. -/
theorem inR : Region.Sub ⟨sA s₀ xIn, w.H.S⟩ (frR s₀) :=
  Offset.sub_base _ (by have := S_le w; have : xFr = 480 := rfl; simp only [xIn]; omega_arith)

omit hp in
theorem outR : Region.Sub ⟨sA s₀ xOut, w.H.S⟩ (frR s₀) :=
  Offset.sub_base _ (by have := S_le w; have : xFr = 480 := rfl; simp only [xOut]; omega_arith)

omit hp in
theorem in_out : Region.Disjoint ⟨sA s₀ xIn, w.H.S⟩ ⟨sA s₀ xOut, w.H.S⟩ := by
  have := S_le w
  exact Offset.disjoint _ (.inl (by simp only [xIn, xOut]; omega_arith)) (by simp only [xIn]; omega_arith)
    (by simp only [xOut]; omega_arith)

omit hp in
/-- The stack a callee uses, within `stk`. -/
theorem below_stk {t : State} (ht : t.sp = s₀.sp) {n : Nat} (hn : n ≤ 512) :
    Region.Sub (below t.sp n) (stk s₀) := by
  rw [ht]; exact Offset.below_mono _ hn (by decide)

/-- The input keying material fits HMAC's count with a block of key. -/
theorem ikm_lt : w.H.B + ikmLen s₀ < 2 ^ 64 := by
  have d : Region.Disjoint ⟨ikm s₀, ikmLen s₀⟩ ⟨s₀.sp - BitVec.ofNat 64 512, 512⟩ := hp.b_i.symm
  have sp := hp.sp
  have e : (s₀.sp - BitVec.ofNat 64 512).toNat = s₀.sp.toNat - 512 :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega_using [sp]) (by decide)
  have h2 : (s₀.sp - BitVec.ofNat 64 512).toNat + 512 ≤ 2 ^ 64 := by
    rw [e]; have := s₀.sp.isLt; omega_using [this, sp]
  have h := VG.Proof.Pbkdf2.Whole.len_add_le d hp.ni h2
  have hB : w.H.B ≤ 128 := by rcases w.hH.hB64 with h | h <;> omega_using [h]
  have h' : ikmLen s₀ + 512 ≤ 2 ^ 64 := h
  omega_using [h', hB]

/-- The loads of the table's functions' addresses. -/
theorem tload0 {t : State} (k : XR w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 0)]) t fun u => Upd t u .t1 (s₀.syms w.hiN) ∧ u.syms = t.syms := by
  have h0 : tab s₀ + BitVec.ofNat 64 (8 * 0) = tab s₀ := by rw [Nat.mul_zero, BitVec.add_zero]
  have := k.tabW hp (o := 0) (by decide)
  rw [BitVec.add_zero] at this
  exact tload_ok (by decide) k.s6 (by rw [h0]; have := tin hp k (o := 0) (by decide); rwa [BitVec.add_zero] at this)
    (by rw [h0]; exact hp.ta) (by rw [h0, this]; exact hp.tmem.1)

theorem tload1 {t : State} (k : XR w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 1)]) t fun u => Upd t u .t1 (s₀.syms w.H.updN) ∧ u.syms = t.syms :=
  tload_ok (by decide) k.s6 (tin hp k (by decide)) (tal hp rfl (by decide))
    (by rw [show (8 * 1 : Nat) = 8 from rfl, k.tabW hp (by decide)]; exact hp.tmem.2.1)

theorem tload2 {t : State} (k : XR w s₀ t) :
    WP isa (.block [.load .d .t1 .s6 (8 * 2)]) t fun u => Upd t u .t1 (s₀.syms w.hfN) ∧ u.syms = t.syms :=
  tload_ok (by decide) k.s6 (tin hp k (by decide)) (tal hp rfl (by decide))
    (by rw [show (8 * 2 : Nat) = 16 from rfl, k.tabW hp (by decide)]; exact hp.tmem.2.2)

/-- `init`, through the table: the states of `K₀`. -/
theorem init_args {t t' : State} (h : XA w s₀ t) {v : Addr} (u : Upd t t' .t1 v) :
    HiArgs w t' (sA s₀ xIn) (sA s₀ xOut) (salt s₀) (saltLen s₀) := by
  obtain ⟨k, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.ibytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.1
  refine ⟨by rw [g _ (by decide), a0], by rw [g _ (by decide), a1], by rw [g _ (by decide), a2],
      by rw [g _ (by decide), a3], by rw [u.sp, k.sp]; exact hp.al,
      by rw [u.sp, k.sp]; have := hp.sp; omega_using [this, hx.1], in_out (w := w) (s₀ := s₀),
      hp.f_s.symm.sub_right (inR (w := w) (s₀ := s₀)), hp.f_s.symm.sub_right (outR (w := w) (s₀ := s₀)),
      (hp.b_f.sub_left hb).sub_right (inR (w := w) (s₀ := s₀)), (hp.b_f.sub_left hb).sub_right (outR (w := w) (s₀ := s₀)),
      hp.b_s.sub_left hb, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.rd, u.wr, k.rd, k.wr, hp.rd, hp.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨saltR s₀, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using []⟩
    · exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
    · exact ⟨frR s₀, by simp, xOut, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xOut]; omega_arith⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, k.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
    · exact ⟨frR s₀, by simp, xOut, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xOut]; omega_arith⟩

theorem init_call {t t' : State} (h : XA w s₀ t) {v : Addr} (u : Upd t t' .t1 v)
    (sy : t'.syms = t.syms) : WP isa (.call w.hiN w.H.init) t' (XI w s₀) := by
  have hh := h
  obtain ⟨k, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.ibytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.1
  refine VG.RISCV64.WP.of_syms <| hi_call (init_args hp hh u) fun s' a hI hO sy' => ?_
  have k' : XR w s₀ s' := (k.upd (by decide) u sy).keep hp a.rd a.wr a.sp sy'
    (fun r hr => a.cs r (kregs_pres r hr)) a.frame
    (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl ⟨xIn, w.H.S, rfl, by decide, by have := S_le w; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
      · exact .inl ⟨xOut, w.H.S, rfl, by decide, by have := S_le w; have : xFr = 480 := rfl; simp only [xOut]; omega_arith⟩
      · exact .inr (.inr ⟨_, by rw [u.sp, k.sp], hx.1⟩))
  have hs : bytesAt t'.mem (salt s₀) (saltLen s₀) = bytesAt s₀.mem (salt s₀) (saltLen s₀) := by
    rw [u.mem]; exact k.saltB hp
  rw [hs] at hI hO
  exact ⟨k', hI, hO⟩

theorem init_ok {t : State} (h : XA w s₀ t) : WP isa (tcall 0 f.init) t (XI w s₀) := by
  have k := h.1
  unfold tcall
  refine WP.seq (WP.mono (tload0 hp k) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (init_call hp h u sy)
  show f.init.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, k.sy]; exact hp.tok.i

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
theorem updArgs_ok {t : State} (h : XI w s₀ t) : WP isa (.block extractUpd) t (XUA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractUpd
  refine VG.RISCV64.WP.of_syms (wp_addi (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_mv fun t₃ u₃ =>
    wp_mv fun t₄ u₄ => WP.block_nil fun sy => ?_)
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : XR w s₀ t₄ := k.same (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]) m₄
  refine ⟨⟨k₄, by rw [m₄]; exact hI, by rw [m₄]; exact hO⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.other, u₃.other, u₂.other, u₁.gpr]; rw [k.s1]
  · upd_simp [u₄.other, u₃.other, u₂.gpr, u₁.other]; exact k.s8
  · upd_simp [u₄.other, u₃.gpr, u₂.other, u₁.other]; exact k.s3
  · upd_simp [u₄.gpr, u₃.other, u₂.other, u₁.other]; exact k.s4

/-- `update`, through the table: the input keying material absorbed. -/
theorem upd_args {t t' : State} (h : XUA w s₀ t) {v : Addr} (u : Upd t t' .t1 v) :
    UpdArgs w t' (sA s₀ xIn) (ikm s₀) (ikmLen s₀) := by
  obtain ⟨⟨k, hI, hO⟩, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp w.H.F) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.2.2
  refine ⟨by rw [g _ (by decide), a0], by rw [g _ (by decide), a2], by rw [g _ (by decide), a3],
      hp.f_i.symm.sub_right (inR (w := w) (s₀ := s₀)), by rw [u.sp, k.sp]; exact hp.al,
      by rw [u.sp, k.sp]; have := hp.sp; omega_using [this, hx.2.2],
      (hp.b_f.sub_left hb).sub_right (inR (w := w) (s₀ := s₀)), hp.b_i.sub_left hb, ?_, ?_⟩
   
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.rd, u.wr, k.rd, k.wr, hp.rd, hp.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ikmR s₀, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using []⟩
    · exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, k.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩

theorem absorb_call {t t' : State} (h : XUA w s₀ t) {v : Addr} (u : Upd t t' .t1 v)
    (sy : t'.syms = t.syms) : WP isa (.call w.H.updN w.H.updC) t' (XU w s₀) := by
  have hh := h
  obtain ⟨⟨k, hI, hO⟩, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp w.H.F) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.2.2
  refine VG.RISCV64.WP.of_syms <| VG.Proof.Hkdf.RISCV64.upd_call (upd_args hp hh u) fun s' a hu sy' => ?_
  have k' : XR w s₀ s' := (k.upd (by decide) u sy).keep hp a.rd a.wr a.sp sy'
    (fun r hr => a.cs r (kregs_pres r hr)) a.frame
    (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨xIn, w.H.S, rfl, by decide, by have := S_le w; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
      · exact .inr (.inr ⟨_, by rw [u.sp, k.sp], hx.2.2⟩))
  have fd : ∀ r ∈ ([⟨sA s₀ xIn, w.H.S⟩] ++ [below t'.sp w.H.F] : List Region),
      Region.Disjoint ⟨sA s₀ xOut, w.H.S⟩ r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (in_out (w := w) (s₀ := s₀)).symm
    · exact ((hp.b_f.sub_left hb).sub_right (outR (w := w) (s₀ := s₀))).symm
  have hm : t'.mem = t.mem := u.mem
  have hl : (xorPad (k0Of w s₀) ipad).length = w.H.B := by rw [xorPad_length, blockKey_length]
  refine ⟨k', ?_, ?_⟩
  · have := hu _ (by rw [hm]; exact hI) (by rw [g _ (by decide), a1, hl])
    rwa [hm, k.ikmB hp] at this
  · exact w.hH.congr _ _ _ _ (fun i hi => a.frame.bytes (R := ⟨sA s₀ xOut, w.H.S⟩) fd
      (by have := S_le w; show w.H.S ≤ 2 ^ 64; omega_using [this]) hi |>.trans (by rw [hm])) hO

theorem upd_ok {t : State} (h : XUA w s₀ t) : WP isa (tcall 1 f.upd) t (XU w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload1 hp k) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (absorb_call hp h u sy)
  show f.upd.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, k.sy]; exact hp.tok.u

end

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

omit hp in
theorem finArgs_ok {t : State} (h : XU w s₀ t) : WP isa (.block extractFin) t (XFA w s₀) := by
  obtain ⟨k, hI, hO⟩ := h
  unfold extractFin
  refine VG.RISCV64.WP.of_syms (wp_addi (by decide) fun t₁ u₁ => wp_addi (by decide) fun t₂ u₂ =>
    wp_add fun t₃ u₃ => wp_mv fun t₄ u₄ => WP.block_nil fun sy => ?_)
  have m₄ : t₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₄ : XR w s₀ t₄ := k.same (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) sy (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        upd_simp [u₄.other, u₃.other, u₂.other, u₁.other]) m₄
  refine ⟨⟨k₄, by rw [m₄]; exact hI, by rw [m₄]; exact hO⟩, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.other, u₃.other, u₂.other, u₁.gpr]; rw [k.s1]
  · upd_simp [u₄.other, u₃.other, u₂.gpr, u₁.other]; rw [k.s1]
  · upd_simp [u₄.other, u₃.gpr, u₂.other, u₁.other]; rw [k.s8, k.s4]
  · upd_simp [u₄.gpr, u₃.other, u₂.other, u₁.other]; exact k.s2

/-- `finalize`, through the table: `PRK`. -/
theorem fin_args {t t' : State} (h : XFA w s₀ t) {v : Addr} (u : Upd t t' .t1 v) :
    HfArgs w t' (sA s₀ xIn) (sA s₀ xOut) (prk s₀) := by
  obtain ⟨⟨k, hI, hO⟩, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.fbytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.2.1
  refine ⟨by rw [g _ (by decide), a0], by rw [g _ (by decide), a1], by rw [g _ (by decide), a3],
      by rw [u.sp, k.sp]; exact hp.al, by rw [u.sp, k.sp]; have := hp.sp; omega_using [this, hx.2.1],
      in_out (w := w) (s₀ := s₀), hp.f_p.sub_left (inR (w := w) (s₀ := s₀)),
      hp.f_p.sub_left (outR (w := w) (s₀ := s₀)),
      (hp.b_f.sub_left hb).sub_right (inR (w := w) (s₀ := s₀)), (hp.b_f.sub_left hb).sub_right (outR (w := w) (s₀ := s₀)),
      hp.b_p.sub_left hb, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.rd, u.wr, k.rd, k.wr, hp.rd, hp.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨frR s₀, by simp, xOut, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xOut]; omega_arith⟩
    · exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
    · exact ⟨prkR w s₀, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using []⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    rw [u.wr, k.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨frR s₀, by simp, xIn, rfl, by have := S_le w; dsimp only; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
    · exact ⟨prkR w s₀, by simp, 0, by rw [BitVec.add_zero], by dsimp only; omega_using []⟩

theorem fin_call {t t' : State} (h : XFA w s₀ t) {v : Addr} (u : Upd t t' .t1 v)
    (sy : t'.syms = t.syms) : WP isa (.call w.hfN w.H.finalize) t' (XF w s₀) := by
  have hh := h
  obtain ⟨⟨k, hI, hO⟩, a0, a1, a2, a3⟩ := h
  have hx := x_le w
  have g : ∀ r, r ≠ .t1 → t'.gpr r = t.gpr r := u.other
  have hb : Region.Sub (below t'.sp (w.H.fbytes + w.H.F)) (stk s₀) := below_stk (by rw [u.sp, k.sp]) hx.2.1
  refine VG.RISCV64.WP.of_syms <| hf_call (fin_args hp hh u) fun s' a hf sy' => ?_
  have k' : XR w s₀ s' := (k.upd (by decide) u sy).keep hp a.rd a.wr a.sp sy'
    (fun r hr => a.cs r (kregs_pres r hr)) a.frame
    (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inl ⟨xIn, w.H.S, rfl, by decide, by have := S_le w; have : xFr = 480 := rfl; simp only [xIn]; omega_arith⟩
      · exact .inr (.inl (fun _ h => h))
      · exact .inr (.inr ⟨_, by rw [u.sp, k.sp], hx.2.1⟩))
  have hm : t'.mem = t.mem := u.mem
  have hl : (k0Of w s₀).length = w.H.B := blockKey_length w _
  have hc : t'.gpr .a2 = BitVec.ofNat 64 (w.H.B + (ikmOf s₀).length) := by
    rw [g _ (by decide), a2, VG.Proof.Hmac.Common.bytesAt_length]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := ikm_lt hp; have hB : w.H.B < 2 ^ 64 := by omega_using [this]
    rw [Nat.mod_eq_of_lt hB]
  refine ⟨k', hf _ _ hl (by rw [hl, VG.Proof.Hmac.Common.bytesAt_length]; exact ikm_lt hp)
    (by rw [hm]; exact hI) hc (by rw [hm]; exact hO)⟩

theorem fin_ok {t : State} (h : XFA w s₀ t) : WP isa (tcall 2 f.fin) t (XF w s₀) := by
  have k := h.1.1
  unfold tcall
  refine WP.seq (WP.mono (tload2 hp k) fun t' ⟨u, sy⟩ => ?_)
  refine WP.icalls_of_call (a := t'.gpr .t1) rfl ?_ (fin_call hp h u sy)
  show f.fin.find? (fun q => t'.syms q.1 == t'.gpr .t1) = _
  rw [u.gpr, sy, k.sy]; exact hp.tok.f

end

/-! ## The epilogue, and the function -/

theorem restorable : Spill.Restorable .s1 restList := by decide

section
variable {w : HVar} {f : Fns} {s₀ : State} (hp : Pre w f s₀)
include hp

/-- The frame's body: our caller's registers restored, and `PRK`. -/
theorem main_ok : WP isa (extractMain f) s₀ fun u => (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧
      u.gpr .ra = s₀.gpr .ra ∧ u.sp = s₀.sp ∧ u.wr = s₀.wr ∧
      bytesAt u.mem (prk s₀) w.H.D = hmacBlockKey w.hH.SH.H (k0Of w s₀) (ikmOf s₀) := by
  have hfr : xFr = 480 := rfl
  unfold extractMain
  refine WP.seq (WP.mono (pro_ok hp) fun t₁ h₁ => WP.seq (WP.mono (init_ok hp h₁) fun t₂ h₂ =>
    WP.seq (WP.mono (updArgs_ok h₂) fun t₃ h₃ => WP.seq (WP.mono (upd_ok hp h₃) fun t₄ h₄ =>
    WP.seq (WP.mono (finArgs_ok h₄) fun t₅ h₅ => WP.seq (WP.mono (fin_ok hp h₅) fun t₆ ⟨k₆, hP⟩ => ?_))))))
  refine WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k₆.s1
    (by decide) restorable
    (fun q hq => in_fr hp k₆.wr (by
      simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
    (k₆.saved.sub (by decide))) fun u hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, k₆.sp], by rw [hr.wr, k₆.wr],
      by rw [hr.mem]; exact hP⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact .inl (by decide) | exact .inr k₆.s11
  · exact hr.gpr_of (.inl (by decide))

end

/-- `vg_hkdf_extract`, in its frame. -/
theorem extract_correct {w : HVar} {f : Fns} {ns : List String} {s : State}
    (hp : (extractR w f ns xStack).pre s) :
    WP isa (extract f) s fun s' => abiPreserved s s' ∧ (extractR w f ns xStack).post s s' := by
  have hfr : xFr = 480 := rfl
  have hsp : xStack ≤ s.sp.toNat := hp.2.2.2.2.2.2.2.1
  obtain p := pre_alloc hp
  unfold extract
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have : xStack = xFr + 512 := rfl; omega_using [hsp, this])
    (WP.mono (main_ok p) fun v ⟨hcs, hra, hvsp, hvwr, hP⟩ m un fl => ?_)
  refine ⟨⟨fun r hr => hcs r hr, ?_, hra⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 xFr = s.sp
    rw [hvsp]; simp only [allocd, BitVec.sub_add_cancel]
  -- The `free` loses the frame's bytes, which lie apart from `prk`.
  obtain e : bytesAt m (s.gpr .a4) w.H.D = bytesAt v.mem (s.gpr .a4) w.H.D :=
    Proof.Sha256.Stream.bytesAt_congr fun i hi => lost_byte fl (R := prkR w (allocd xFr s)) p.f_p.symm hi
  show bytesAt m (s.gpr .a4) w.H.D = Spec.Hmac.hmac _ _ _
  rw [e]
  exact hP

/-! ## Constant time -/

/-- The registers `XR` fixes that hold the pointers and lengths. -/
abbrev pubRegs : List Reg := [.s1, .s2, .s3, .s4, .s6, .s7, .s8]

/-- The taint checks of the pieces of `vg_hkdf_extract` between the calls. -/
structure XChecks : Prop where
  pro : Ck [.a0, .a1, .a2, .a3, .a4, .a5, .a6] (.block extractPro)
  tl0 : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 0)])
  tl1 : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 1)])
  tl2 : Ck [.s6] (.block [.load .d .t1 .s6 (8 * 2)])
  ua : Ck pubRegs (.block extractUpd)
  fa : Ck pubRegs (.block extractFin)
  epi : Ck [.s1] (.block restore)

theorem xchecks : XChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨?_, ?_⟩
  taint_decide_all

/-- The public data of two runs, from the start of the frame's body. -/
structure PubEq (w : HVar) (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  regs : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6], s₀.gpr r = s₀'.gpr r
  hi : s₀.syms w.hiN = s₀'.syms w.hiN
  up : s₀.syms w.H.updN = s₀'.syms w.H.updN
  hf : s₀.syms w.hfN = s₀'.syms w.hfN

section
variable {w : HVar} {f : Fns} {s₀ s₀' : State} (hp : Pre w f s₀) (hp' : Pre w f s₀')
  (hq : PubEq w s₀ s₀')
include hp hp' hq

omit hp hp' in
theorem ag {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') : t.sp = t'.sp ∧ ∀ r ∈ pubRegs, t.gpr r = t'.gpr r := by
  refine ⟨by rw [k.sp, k'.sp, hq.sp], fun r hr => ?_⟩
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [k.s1, k'.s1, hq.sp]
  · rw [k.s2, k'.s2]; exact hq.regs .a4 (by simp)
  · rw [k.s3, k'.s3]; exact hq.regs .a2 (by simp)
  · rw [k.s4, k'.s4]; exact hq.regs .a3 (by simp)
  · rw [k.s6, k'.s6]; exact hq.regs .a6 (by simp)
  · rw [k.s7, k'.s7]
  · rw [k.s8, k'.s8]

omit hp hp' in
theorem ag6 {t t' : State} (k : XR w s₀ t) (k' : XR w s₀' t') :
    t.sp = t'.sp ∧ ∀ r ∈ [Reg.s6], t.gpr r = t'.gpr r :=
  ⟨(ag hq k k').1, fun r hr => (ag hq k k').2 r (by simp at hr; subst hr; simp)⟩

/-- The frame's body leaks the same trace in both runs. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (extractMain f) fun _ _ => True := by
  have kc := xchecks
  have e0 := hq.regs .a0 (by simp); have e1 := hq.regs .a1 (by simp); have e2 := hq.regs .a2 (by simp)
  have e3 := hq.regs .a3 (by simp); have e4 := hq.regs .a4 (by simp)
  have esp := hq.sp
  unfold extractMain
  have r1 := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀') (G₁ := XA w s₀) (G₂ := XA w s₀')
    (rs := [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (fun s s' hs hs' => by
      subst hs hs'; exact ⟨hq.sp, hq.regs⟩) kc.pro
    (fun s hs => by subst hs; exact pro_ok hp) (fun s hs => by subst hs; exact pro_ok hp')
  have r2 : RelCT isa (fun t t' => XA w s₀ t ∧ XA w s₀' t') (tcall 0 f.init) fun t t' => XI w s₀ t ∧ XI w s₀' t' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.hiN) kc.tl0 (fun t t' k k' => ag6 hq k.1 k'.1)
      (fun t k => tload0 hp k.1) (fun t k => by rw [hq.hi]; exact tload0 hp' k.1)
      (fun t k => by rw [k.1.sy]; exact hp.tok.i) (fun t k => by rw [k.1.sy, hq.hi]; exact hp'.tok.i)
      (hi_rel fun u u' ⟨⟨t, k, v, _⟩, ⟨t', k', v', _⟩⟩ => ⟨init_args hp k v,
        by have := init_args hp' k' v'; simp only [sA, salt, saltLen] at this ⊢; rwa [← e0, ← e1, ← esp] at this,
        by rw [v.sp, v'.sp, k.1.sp, k'.1.sp, esp]⟩))
      (fun t k => init_ok hp k) (fun t k => init_ok hp' k)
  have r3 := rel_agree (P₁ := XI w s₀) (P₂ := XI w s₀') (G₁ := XUA w s₀) (G₂ := XUA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.ua (fun t k => updArgs_ok k) (fun t k => updArgs_ok k)
  have r4 : RelCT isa (fun t t' => XUA w s₀ t ∧ XUA w s₀' t') (tcall 1 f.upd) fun t t' => XU w s₀ t ∧ XU w s₀' t' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.H.updN) kc.tl1 (fun t t' k k' => ag6 hq k.1.1 k'.1.1)
      (fun t k => tload1 hp k.1.1) (fun t k => by rw [hq.up]; exact tload1 hp' k.1.1)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.u) (fun t k => by rw [k.1.1.sy, hq.up]; exact hp'.tok.u)
      (upd_rel fun u u' ⟨⟨t, k, v, _⟩, ⟨t', k', v', _⟩⟩ => ⟨upd_args hp k v,
        by have := upd_args hp' k' v'; simp only [sA, ikm, ikmLen] at this ⊢; rwa [← e2, ← e3, ← esp] at this,
        by rw [v.sp, v'.sp, k.1.1.sp, k'.1.1.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), k.2.2.1, k'.2.2.1]⟩))
      (fun t k => upd_ok hp k) (fun t k => upd_ok hp' k)
  have r5 := rel_agree (P₁ := XU w s₀) (P₂ := XU w s₀') (G₁ := XFA w s₀) (G₂ := XFA w s₀') (rs := pubRegs)
    (fun t t' k k' => ag hq k.1 k'.1) kc.fa (fun t k => finArgs_ok k) (fun t k => finArgs_ok k)
  have r6 : RelCT isa (fun t t' => XFA w s₀ t ∧ XFA w s₀' t') (tcall 2 f.fin) fun t t' => XF w s₀ t ∧ XF w s₀' t' :=
    rel_wp (tcall_rel (rs := [.s6]) (a := s₀.syms w.hfN) kc.tl2 (fun t t' k k' => ag6 hq k.1.1 k'.1.1)
      (fun t k => tload2 hp k.1.1) (fun t k => by rw [hq.hf]; exact tload2 hp' k.1.1)
      (fun t k => by rw [k.1.1.sy]; exact hp.tok.f) (fun t k => by rw [k.1.1.sy, hq.hf]; exact hp'.tok.f)
      (hf_rel fun u u' ⟨⟨t, k, v, _⟩, ⟨t', k', v', _⟩⟩ => ⟨fin_args hp k v,
        by have := fin_args hp' k' v'; simp only [sA, prk] at this ⊢; rwa [← e4, ← esp] at this,
        by rw [v.sp, v'.sp, k.1.1.sp, k'.1.1.sp, esp],
        by rw [v.other _ (by decide), v'.other _ (by decide), k.2.2.2.1, k'.2.2.2.1, e3]⟩))
      (fun t k => fin_ok hp k) (fun t k => fin_ok hp' k)
  have r7 := rel_agree (P₁ := XF w s₀) (P₂ := XF w s₀') (G₁ := fun _ => True) (G₂ := fun _ => True) (rs := [.s1])
    (fun t t' k k' => ⟨by rw [k.1.sp, k'.1.sp, esp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [k.1.s1, k'.1.s1, esp]⟩) kc.epi
    (fun t k => by
      have hfr : xFr = 480 := rfl
      exact WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp.al]) k.1.s1 (by decide) restorable
        (fun q hq => in_fr hp k.1.wr (by
          simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
        (k.1.saved.sub (by decide))) fun _ _ => trivial)
    (fun t k => by
      have hfr : xFr = 480 := rfl
      exact WP.mono (Spill.restore_wp (b := .s1) (l := restList) (by omega_using [hp'.al]) k.1.s1 (by decide) restorable
        (fun q hq => in_fr hp' k.1.wr (by
          simp only [restList, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega_using [hfr]))
        (k.1.saved.sub (by decide))) fun _ _ => trivial)
  exact ((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ _ => trivial)

end

/-- `vg_hkdf_extract` is constant time: two runs whose public data agree
leak the same trace. -/
theorem extract_ct {w : HVar} {f : Fns} {ns : List String} (hns : ∀ n ∈ [w.hiN, w.H.updN, w.hfN], n ∈ ns) :
    ConstantTime isa (extractR w f ns xStack).pre (extractR w f ns xStack).pub (extract f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨qsp, q0, q1, q2, q3, q4, q5, q6, qn⟩ := hpub
  have hq : PubEq w (allocd xFr e) (allocd xFr e') :=
    ⟨by simp only [allocd, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0, q1, q2, q3, q4, q5, q6], qn _ (hns _ (by simp)), qn _ (hns _ (by simp)), qn _ (hns _ (by simp))⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (extract f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold extract
  refine rel_alloc ((main_rel hp hp' hq).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

end VG.Proof.Hkdf.RISCV64.Extract
