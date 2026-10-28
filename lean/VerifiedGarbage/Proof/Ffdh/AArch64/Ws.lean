module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.Defs.PartialOrder
import VerifiedGarbage.Proof.Framework.Contract

/-!
# FFDH on AArch64: the workspaces

The outer workspace at `B` (`Outer`: `w` words, its header from `head`, and
room after its arrays for the inner one with a 32-entry table), and the
inner one at `off B (slot w 8)` for a modulus: `wsSetup` lays it out and
enters it (`wsSetup_ok`), `modSetup` loads the modulus and computes
`-m⁻¹` and the number 1 (`modSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

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

/-- The outer workspace at `B`, its base in `x0`: `w` words, its header from
`head`, and room for the inner workspace and its table. -/
structure Outer (t : State) (B : Addr) (Z w : Nat) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  hw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  harr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  room : inner w + slot w 8 + tabBytes32 w ≤ Z
  w2 : 2 ≤ w
  w28 : w < 2 ^ 28

theorem Outer.ld {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w) {i : Nat} (hi : i < 32) :
    InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 :=
  h.scr.ld (by have := hdr_lt_slot w 8 hi; have := h.room; omega_arith)

theorem Outer.st {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w) {i : Nat} (hi : i < 32) :
    InRegions t.wr (off B (8 * i)) 8 :=
  h.scr.st (by have := hdr_lt_slot w 8 hi; have := h.room; omega_arith)

/-- What changes only the outer header's slots from `sFn 0` on, outside the
inner workspace keeps `Outer`. -/
theorem Outer.of_frm {s t : State} {B : Addr} {Z w : Nat} {rs : List (Nat × Nat)} (h : Outer s B Z w)
    (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ Z) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : Outer t B Z w := by
  have hn := h.scr.nowrap
  have hh : ∀ i < 16, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by have := h.room; unfold inner slot hdrBytes at this; omega_arith)
  exact ⟨h.scr.congr hwr, h0.trans h.x0, (hh _ (by decide)).trans h.hw,
    fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (h.harr j hj), h.room, h.w2, h.w28⟩

/-- `SubCtx` after a change of `-m⁻¹` and of the inner workspace's own
slots and arrays. -/
theorem _root_.VG.Proof.Bignum.AArch64.SubCtx.of_minv {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r = (8 * sMinv, 8) ∨ (8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx))
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) :
    SubCtx t B Z o w wx (word t.mem (off B o) (8 * sMinv)) := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have hL : o + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64 := by omega_arith
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + tabBytes wx := fun r hr' => by
    rcases hr r hr' with rfl | h
    · have := hdr_lt_slot wx 8 (show sMinv < 32 by decide); simp only; omega_arith
    · exact h.2
  have hh : ∀ i < 17, i ≠ sMinv → word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' hne =>
    hf.word_eq (fun r hr'' => by
      rcases hr r hr'' with rfl | h
      · simp only; unfold sMinv at hne ⊢; omega_arith
      · exact Or.inl (by omega_arith))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
          omega_arith)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega_arith) (by have := hdr_lt_slot w 8 hi'; omega_arith)
  exact ⟨h.scr.congr hwr, h0.trans h.x0,
    ⟨(hh _ (by decide) (by decide)).trans h.hdr.hw, rfl,
      fun j hj => (hh _ (by unfold sArr; omega_arith) (by unfold sArr sMinv; omega_arith)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide) (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_arith)).trans (h.narr j hj), h.lo, h.hi⟩

/-! ## `wsSetup` -/

/-- `wsSetup sl` and the entry into the inner workspace, for a modulus of
`len` octets (the length in the outer slot `sl`). -/
theorem wsSetup_ok {s : State} {B : Addr} {Z w : Nat} (h : Outer s B Z w) {sl len : Nat} (hsl : sl < 32)
    (hne : sl ≠ sWs) (hlen : word s.mem B (8 * sl) = BitVec.ofNat 64 len) (_hlen1 : 1 ≤ len) (hlenw : len ≤ 8 * w) :
    WP isa (.block (wsSetup sl ++ [enter])) s fun t =>
      SubCtx t B Z (inner w) w (wsWords len) (word t.mem (off B (inner w)) (8 * sMinv)) ∧
      word t.mem B (8 * sWs) = off B (inner w) ∧
      Frm B [(8 * sWs, 8), (inner w, 8 * 17)] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have hroom := h.room
  have hw28 := h.w28
  have hwx : wsWords len ≤ w := by unfold wsWords; have := h.w2; omega_arith
  have htab : tabBytes (wsWords len) ≤ tabBytes32 w := by unfold tabBytes tabBytes32; omega_arith
  have hsl8 : slot (wsWords len) 8 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  have hroom' : slot w 8 + slot w 8 + tabBytes32 w ≤ Z := h.room
  have h8s := hdr_lt_slot w 8 (show sWs < 32 by decide)
  unfold wsSetup
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = B ∧ t.mem = s.mem) (by brun [h.x0]) (by decide)
    (by decide) (by decide +kernel)) fun s₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wsEnd_ok (wx := w) (h.scr.congr k₁.wr) h5₁ (by rw [hm₁]; exact h.hw) (by omega_arith)
    (by rw [hm₁]; exact h.harr _ (by decide)) (by omega_arith)) fun s₂ ⟨⟨h4₂, _, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hm12 : s₂.mem = s.mem := hm₂.trans hm₁
  rw [WP.block_append_iff]
  refine WP.mono (wsNew_ok (o := inner w) (len := len) (h.scr.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h.x0) h4₂
    (by decide) hsl (Ne.symm hne) (by rw [hm12]; exact hlen) (by omega_arith)
    (by unfold inner slot hdrBytes; omega_arith) (show slot w 8 + slot (wsWords len) 8 ≤ Z by omega_arith))
    fun s₃ ⟨hWs₃, hl₃, hw₃, ha₃, h0₃, f₃, k₃⟩ => ?_
  have k13 := k12.trans k₃
  have hs₃ := h.scr.congr k13.wr
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B (inner w) ∧ t.mem = s₃.mem)
    (by brun [enter, h0₃, hdr_enc (show sWs < 32 by decide), hs₃.ld (d := 8 * sWs) (by omega_arith), hWs₃])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  have K := k13.trans k
  have f : Frm B [(8 * sWs, 8), (inner w, 8 * 17)] s.mem t.mem := by rw [hm, ← hm12]; exact f₃
  have hb : ∀ i < 32, i ≠ sWs → word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hne' =>
    f.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only; unfold sWs sFn at hne' ⊢; omega_arith
      · simp only; unfold inner slot hdrBytes; omega_arith) (by omega_arith)
  refine ⟨⟨h.scr.congr K.wr, h0, ⟨by rw [hm]; exact hw₃, rfl, fun j hj => by rw [hm]; exact ha₃ j hj⟩,
    by rw [hm]; exact hl₃, by rw [hb _ (by decide) (by decide)]; exact h.hw,
    fun j hj => by rw [hb _ (by unfold sArr; omega_arith) (by unfold sArr sWs sFn; omega_arith)]; exact h.harr j hj,
    Nat.le_refl _, show slot w 8 + slot (wsWords len) 8 + tabBytes (wsWords len) ≤ Z by omega_arith⟩, by rw [hm]; exact hWs₃, f,
    K.mono (by decide)⟩

/-- `-m⁻¹` into the header, and `setWord`'s operands for the number 1. -/
theorem minvBlock_ok {t : State} {G : Addr} {Zx wx : Nat} {mi : BitVec 64} (hg : Good t G Zx wx mi)
    (hZ : slot wx 8 ≤ Zx) (hodd : (word t.mem G (slot wx Public.aN)).toNat % 2 = 1) :
    WP isa (.block ([ldh .x8 (sArr Public.aN), ld .x3 .x8] ++ minv ++
        [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0])) t fun t' =>
      ((word t.mem G (slot wx Public.aN)).toNat * (t'.gpr .x15).toNat + 1) % 2 ^ 64 = 0 ∧
      t'.mem = t.mem.writeW (off G (8 * sMinv)) (t'.gpr .x15) ∧
      t'.gpr .x12 = BitVec.ofNat 64 wx ∧ (t'.gpr .x9).toNat = 1 ∧ t'.gpr .x13 = BitVec.ofNat 64 0 ∧
      Keep mmRegs t t' := by
  have hn := hg.scr.nowrap
  have hN := Nat.le_trans (slot_le (w := wx) (show Public.aN < 8 by decide)) hZ
  have hW := hdr_lt_slot wx Public.aN (show sW < 32 by decide)
  have hW' := hdr_lt_slot wx Public.aN (show sMinv < 32 by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x8] (Q := fun t₁ => t₁.gpr .x3 = word t.mem G (slot wx Public.aN) ∧
      t₁.mem = t.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hg.ld hZ (sArr_lt (show Public.aN < 8 by decide)),
      hg.hdr.harr Public.aN (by decide), hg.scr.ld (show slot wx Public.aN + 8 ≤ Zx by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok t₁ (by rw [h3]; exact hodd)) fun t₂ ⟨hinv, k₂, hm₂⟩ => ?_
  rw [h3] at hinv
  have k12 := k₁.trans k₂
  have h0₂ : t₂.gpr .x0 = G := (k12.gpr .x0 (by decide)).trans hg.x0
  have hs₂ : Scr t₂ G Zx := hg.scr.congr k12.wr
  have hw₂' : word (t₂.mem.writeW (off G (8 * sMinv)) (t₂.gpr .x15)) G (8 * sW) = BitVec.ofNat 64 wx := by
    rw [(writeW_outside t₂.mem G _ (by omega_arith)).word (by unfold sW sMinv; omega_arith) (by omega_arith), hm₂, hm₁]
    exact hg.hdr.hw
  refine WP.mono (WP.keep [.x9, .x12, .x13] (Q := fun t' =>
      t'.mem = t₂.mem.writeW (off G (8 * sMinv)) (t₂.gpr .x15) ∧ t'.gpr .x12 = BitVec.ofNat 64 wx ∧
      (t'.gpr .x9).toNat = 1 ∧ t'.gpr .x13 = BitVec.ofNat 64 0)
    (by brun [h0₂, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₂.st (show 8 * sMinv + 8 ≤ Zx by have := hdr_lt_slot wx 8 (show sMinv < 32 by decide); omega_arith),
      hs₂.ld (show 8 * sW + 8 ≤ Zx by have := hdr_lt_slot wx 8 (show sW < 32 by decide); omega_arith), hw₂'])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨hm₃, h12, h9, h13⟩, k₃⟩ => ?_
  have h15₃ : t₃.gpr .x15 = t₂.gpr .x15 := k₃.gpr .x15 (by decide)
  refine ⟨by rw [h15₃]; exact hinv, by rw [hm₃, hm₂, hm₁, h15₃], h12, h9, h13, (k12.trans k₃).mono (by decide)⟩

/-! ## `modSetup` -/

/-- The inner workspace's modulus, `-m⁻¹` and the number 1 (`XVals`). -/
theorem modSetup_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubCtx s B Z o w wx mi)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw28 : w < 2 ^ 28) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {p : Addr}
    {bs : List Byte} (hp : word s.mem B (8 * sp) = p) (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length) (hkw : (bs.length + 7) / 8 ≤ wx)
    (hodd : Spec.Rsa.os2ip bs % 2 = 1) :
    WP isa (seqs (modSetup sp sl)) s fun t => ∃ minv', SubCtx t B Z o w wx minv' ∧
      XVals t B o wx minv' (Spec.Rsa.os2ip bs) ∧
      Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2)), (slot wx Public.aOne, 8 * (wx + 2)), (8 * sMinv, 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hGn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  have sN := slot_le (w := wx) (show Public.aN < 8 by decide)
  have sO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  have hN0 := hdr_lt_slot wx Public.aN (show 31 < 32 by decide)
  have hO0 := hdr_lt_slot wx Public.aOne (show 31 < 32 by decide)
  have sNO := Rsa.slot_lt (w := wx) (show Public.aN < Public.aOne by decide)
  have eMi : sMinv = 7 := rfl
  have hk' : bs.length < 2 ^ 31 := by have h1 := hkw; have h2 := hwx; have h3 := hw28; omega_arith
  unfold modSetup
  refine wp_seqs_append (by simp [loadArr]) (by simp) ?_
  refine WP.mono (primeLoad_ok hc hw2 hwx (by omega_arith) (show Public.aN < 8 by decide) hsp hsl hp hl hsrc hk1 hk' hkw)
    fun s₁ ⟨hc₁, hX₁, ho₁, k₁⟩ => ?_
  simp only [seqs]
  -- `-m⁻¹` and the operands of `setWord`.
  have hodd₁ : (word s₁.mem (off B o) (slot wx Public.aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ wx by omega_arith), hX₁, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd
  refine WP.seq (WP.mono (minvBlock_ok hc₁.good (Nat.le_refl _) hodd₁)
    fun s₄ ⟨hinv, hm₄, h12₄, h9₄, h13₄, k₄⟩ => ?_)
  have o₄ := writeW_outside s₁.mem (off B o) (d := 8 * sMinv) (s₄.gpr .x15) (by decide)
  rw [← hm₄] at o₄
  have f₁₄ : Frm (off B o) [(8 * sMinv, 8)] s₁.mem s₄.mem := Frm.of_outside o₄ (by simp)
  have hc₄ := hc₁.of_minv f₁₄ (fun r hr => Or.inl (List.mem_singleton.mp hr)) k₄.wr (k₄.gpr .x0 (by decide))
  have hmv : word s₄.mem (off B o) (8 * sMinv) = s₄.gpr .x15 := by rw [hm₄]; exact word_writeW_self _ _ _ _
  rw [hmv] at hc₄
  refine WP.mono (setWord_ok hc₄.good.scr hc₄.x0 hc₄.hdr (Nat.le_refl _) h12₄ (by omega_arith) (o := Public.aOne)
    (by decide) (i := 0) (by omega_arith) h13₄) fun t ⟨hone, ho₇, k₇⟩ => ?_
  have f₇ : Frm (off B o) [(slot wx Public.aOne, 8 * (wx + 2))] s₄.mem t.mem := Frm.of_outside ho₇ (by simp)
  have hc₇ := hc₄.of_frm f₇ (fun r hr => by rw [List.mem_singleton.mp hr]; omega_arith) k₇.wr (k₇.gpr .x0 (by decide))
  have f₀₁ : Frm (off B o) [(slot wx Public.aN, 8 * (wx + 2))] s.mem s₁.mem := Frm.of_outside ho₁ (by simp)
  have hN₇ : wv t.mem (off B o) (slot wx Public.aN) wx = Spec.Rsa.os2ip bs := by
    rw [f₇.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; omega_arith) (by omega_arith),
      f₁₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; rw [eMi]; omega_arith) (by omega_arith)]
    exact hX₁
  have hw₇ : word t.mem (off B o) (slot wx Public.aN) = word s₁.mem (off B o) (slot wx Public.aN) := by
    rw [f₇.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; omega_arith) (by omega_arith),
      f₁₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; rw [eMi]; omega_arith) (by omega_arith)]
  refine ⟨s₄.gpr .x15, hc₇, ⟨hN₇, by rw [hw₇]; exact hinv, by rw [hone, h9₄]⟩,
    ((f₀₁.append f₁₄).append f₇).mono (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]),
    ((k₁.trans k₄).trans k₇).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64
