module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # FFDH on x86-64: the nested workspaces -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The inner workspace's offset. -/
abbrev inner (w : Nat) : Nat := slot w 8

/-- `Keep` of the same registers, composed. -/
theorem keep_trans {rs : List Reg} {a b c : State} (h₁ : Keep rs a b) (h₂ : Keep rs b c) : Keep rs a c :=
  (h₁.trans h₂).mono fun _ hr => (List.mem_append.mp hr).elim id id

theorem wp_seqs_cons {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa e s fun t => WP isa (seqs l) t Q) : WP isa (seqs (e :: l)) s Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact WP.seq h

theorem seqs_cons_ct {P Q : State → State → Prop} {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ [])
    (h : RelCT isa P (.seq e (seqs l)) Q) : RelCT isa P (seqs (e :: l)) Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact h

/-- The outer workspace at `B`, its base in `rdi`: `w` words, its header from
`head`, and room for the inner workspace and its table. -/
structure Outer (t : State) (B : Addr) (Z w : Nat) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  harr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  room : inner w + slot w 8 + tabBytes w 32 ≤ Z
  w2 : 2 ≤ w
  w28 : w < 2 ^ 28

theorem Outer.ld {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w) {i : Nat} (hi : i < 32) :
    InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 :=
  h.scr.ld (by have := hdr_lt_slot w 8 hi; have := h.room; omega)

theorem Outer.st {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w) {i : Nat} (hi : i < 32) :
    InRegions t.wr (off B (8 * i)) 8 :=
  h.scr.st (by have := hdr_lt_slot w 8 hi; have := h.room; omega)

/-- What changes only the outer header's slots from `sFn 0` on, outside the
inner workspace keeps `Outer`. -/
theorem Outer.of_frm {s t : State} {B : Addr} {Z w : Nat} {rs : List (Nat × Nat)} (h : Outer s B Z w)
    (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ Z) (hwr : t.wr = s.wr)
    (h0 : t.gpr .rdi = s.gpr .rdi) : Outer t B Z w := by
  have hn := h.scr.nowrap
  have hh : ∀ i < 16, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega)) (by have := h.room; unfold inner slot hdrBytes at this; omega)
  exact ⟨h.scr.congr hwr, h0.trans h.rdi, (hh _ (by decide)).trans h.hw,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (h.harr j hj), h.room, h.w2, h.w28⟩

/-- `SubCtx` after a change of `-m⁻¹` and of the inner workspace's own
slots and arrays. -/
theorem _root_.VG.Proof.Bignum.X86_64.SubCtx.of_minv {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r = (8 * sMinv, 8) ∨ (8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx))
    (hwr : t.wr = s.wr) (h0 : t.gpr .rdi = s.gpr .rdi) :
    SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have hL : o + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64 := by omega
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + tabBytes wx := fun r hr' => by
    rcases hr r hr' with rfl | h
    · have := hdr_lt_slot wx 8 (show sMinv < 32 by decide); simp only; omega
    · exact h.2
  have hh : ∀ i < 17, i ≠ sMinv → word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' hne =>
    hf.word_eq (fun r hr'' => by
      rcases hr r hr'' with rfl | h
      · simp only; unfold sMinv at hne ⊢; omega
      · exact Or.inl (by omega))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega
          omega)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega) (by have := hdr_lt_slot w 8 hi'; omega)
  exact ⟨h.scr.congr hwr, h0.trans h.rdi,
    ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw, rfl,
      fun j hj => (hh _ (by unfold sArr; omega) (by unfold sArr sMinv; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), h.lo, h.hi⟩


/-- Lay out the inner workspace and enter it, with room for all 32 powers. -/
theorem wsSetup_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w)
    {sl len : Nat} (hsl : sl < 32) (hne : sl ≠ sWs)
    (hlen : word s.mem B (8 * sl) = BitVec.ofNat 64 len)
    (hlen1 : 1 ≤ len) (hlenw : len ≤ 8 * w) :
    WP isa (seqs (wsSetup sl ++ ([.block [enter]] : List (Prog isa)))) s fun t =>
      SubCtx t B Z (inner w) w (wsWords len) (word t.mem (off B (inner w)) (8 * sMinv)) ∧
      inner w + slot (wsWords len) 8 + tabBytes (wsWords len) 32 ≤ Z ∧
      word t.mem B (8 * sWs) = off B (inner w) ∧
      Frm B [(8 * sWs, 8), (inner w, 8 * 17)] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have hroom := h.room
  have hw28 := h.w28
  have hwx : wsWords len ≤ w := by unfold wsWords; have := h.w2; omega
  have htab : tabBytes (wsWords len) 32 ≤ tabBytes w 32 := by unfold tabBytes; omega
  have hsl8 : slot (wsWords len) 8 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have htab16 : tabBytes (wsWords len) 16 ≤ tabBytes (wsWords len) 32 := by unfold tabBytes; omega
  unfold wsSetup
  simp only [List.cons_append, List.nil_append]
  refine WP.seq ?_
  rw [show (.mov .rdx (.reg .rdi) :: wsEnd) = ([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = B ∧ t.mem = s.mem)
    (by xrun [h.rdi]) rfl) fun s₁ ⟨⟨hdx, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEnd_ok (wx := w) (h.scr.congr k₁.2.2) hdx (by rw [hm₁]; exact h.hw)
    (by rw [hm₁]; exact h.harr _ (by decide)) (by omega)) fun s₂ ⟨hax, hm₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hm12 : s₂.mem = s.mem := hm₂.trans hm₁
  refine wp_seqs_append (by simp [wsNew]) (by simp) ?_
  refine WP.mono (wsNew_ok (o := inner w) (len := len) (h.scr.congr k12.2.2)
    ((k12.gpr (by decide)).trans h.rdi) hax (by decide) hsl (Ne.symm hne)
    (by rw [hm12]; exact hlen) (by omega) (by unfold inner slot hdrBytes; omega)
    (show inner w + slot (wsWords len) 8 ≤ Z by omega))
    fun s₃ ⟨hWs, hl, hw, ha, hdi, f₃, k₃⟩ => ?_
  have k13 := k12.trans k₃
  have hs₃ := h.scr.congr k13.2.2
  simp only [seqs]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B (inner w) ∧ t.mem = s₃.mem)
    (by unfold enter; xrun [State.ea, hdr, hdi, hdrOff,
      hs₃.ld (d := 8 * sWs) (by have := hdr_lt_slot w 8 (show sWs < 32 by decide); omega), hWs]) rfl)
    fun t ⟨⟨hdi', hm⟩, k⟩ => ?_
  have K := k13.trans k
  have f : Frm B [(8 * sWs, 8), (inner w, 8 * 17)] s.mem t.mem := by rw [hm, ← hm12]; exact f₃
  have hb : ∀ i < 32, i ≠ sWs → word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne' =>
    f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; unfold sWs sFn at hne' ⊢; omega
      · simp only; unfold inner slot hdrBytes; omega) (by omega)
  refine ⟨⟨h.scr.congr K.2.2, hdi', ⟨by rw [hm]; exact hw, rfl,
    fun j hj => by rw [hm]; exact ha j hj⟩, by rw [hm]; exact hl,
    by rw [hb _ (by decide) (by decide)]; exact h.hw,
    fun j hj => by rw [hb _ (by unfold sArr; omega) (by unfold sArr sWs sFn; omega)]; exact h.harr j hj,
    le_refl _, by omega⟩, by omega, by rw [hm]; exact hWs, f, K.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64
