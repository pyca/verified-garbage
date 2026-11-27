module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ffdh.AArch64.Pow`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Ws`, which this module and modules that import it used -/

section

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

end

end

/-!
# FFDH on AArch64: an exponentiation

`pow bp bl ep el` in the inner workspace for a modulus `X`, with `R² mod X`
in `aR2`: the base (pointer and length in the outer slots `bp`, `bl`) into
`aXm`; the accumulator `R mod X` and the base in Montgomery form; `R²` kept
in `aX` while the base takes `aXc` (array `aR2`); RSA's five-bit
exponentiation over every octet of the exponent (slots `ep`, `el`); the
result out of Montgomery form; `R²` back (`pow_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The inner workspace for the modulus `X`, `-X⁻¹`, the number 1 and
`R² mod X`. -/
structure ModCtx (t : State) (B : Addr) (Z o w : Nat) (mi : BitVec 64) (X : Nat) : Prop where
  sub : SubCtx t B Z o w w mi
  xv : XVals t B o w mi X
  r2l : wv t.mem (off B o) (slot w aR2) w < X
  r2 : wv t.mem (off B o) (slot w aR2) w % X = 2 ^ (64 * w) * 2 ^ (64 * w) % X
  odd : X % 2 = 1
  x1 : 1 < X
  wide : o + slot w 8 + tabBytes32 w ≤ Z
  w2 : 2 ≤ w
  w28 : w < 2 ^ 28

/-- What `pow` changes in the inner workspace. -/
def powRanges (w : Nat) : List (Nat × Nat) :=
  (slot w aX, 8 * (w + 2)) :: (slot w aR2, 8 * (w + 2)) :: (slot w aXm, 8 * (w + 2)) :: CrtWindowFive.crtExpRanges w

theorem powRanges_ok (w : Nat) : ∀ r ∈ powRanges w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 + tabBytes32 w := by
  intro r hr
  simp only [powRanges, List.mem_cons] at hr
  obtain h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  obtain s0 := slot_le (w := w) (show aX < 8 by decide)
  obtain s1 := slot_le (w := w) (show aR2 < 8 by decide)
  obtain s2 := slot_le (w := w) (show aXm < 8 by decide)
  obtain g1 := slot_le (w := w) (show 0 < 8 by decide)
  obtain e0 : slot w 0 = 256 := by unfold slot hdrBytes; omega_arith
  rcases hr with rfl | rfl | rfl | hr
  · have := hdr_lt_slot w aX (show 31 < 32 by decide); simp only; unfold tabBytes32; omega_arith
  · have := hdr_lt_slot w aR2 (show 31 < 32 by decide); simp only; unfold tabBytes32; omega_arith
  · have := hdr_lt_slot w aXm (show 31 < 32 by decide); simp only; unfold tabBytes32; omega_arith
  · exact CrtWindowFive.crtExpRanges_ok w r hr

/-- `XVals` after a change of memory outside the modulus, the number 1 and the
header's first 17 slots. -/
theorem _root_.VG.Proof.Bignum.AArch64.XVals.of_frmA {s t : State} {B : Addr} {o w : Nat} {mi : BitVec 64} {X : Nat} {rs : List (Nat × Nat)}
    (h : XVals s B o w mi X) (hn : (off B o).toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w)
    (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1)) : XVals t B o w mi X := by
  obtain sN := slot_le (w := w) (show aN < 8 by decide)
  obtain sO := slot_le (w := w) (show aOne < 8 by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [hf.wv_eq (fun r hr' => by have := (hr r hr').1; omega_arith) (by omega_arith)]; exact h.n
  · rw [hf.word_eq (fun r hr' => by have := (hr r hr').1; omega_arith) (by omega_arith)]; exact h.inv
  · rw [hf.wv_eq (fun r hr' => by have := (hr r hr').2; omega_arith) (by omega_arith)]; exact h.one

/-- The ranges of arrays other than the modulus and the number 1. -/
theorem arr_off (w : Nat) {j : Nat} (h0 : j ≠ aN) (h7 : j ≠ aOne) :
    ((slot w j + 8 * (w + 2) ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ slot w j) ∧
      (slot w j + 8 * (w + 2) ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ slot w j)) :=
  ⟨slot_sep (w := w) h0, slot_sep (w := w) h7⟩

/-- A change of the inner workspace (with its table) keeps the outer header,
and memory past the inner workspace. -/
theorem child_frm {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (hc : SubCtx s B Z o w w mi) (hwide : o + slot w 8 + tabBytes32 w ≤ Z) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot w 8 + tabBytes32 w) :
    (∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i)) ∧ InScr B Z s.mem t.mem := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  obtain hL : o + (slot w 8 + tabBytes32 w) ≤ 2 ^ 64 := by omega_arith
  obtain h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  refine ⟨fun i hi => hf.word_below hr hL (by unfold slot hdrBytes at hL; omega_arith)
    (by have := hdr_lt_slot w 8 hi; omega_arith), ?_⟩
  refine InScr.of_frm (hf.rebase (by omega_arith) fun r hr' => by have := hr r hr'; omega_arith) fun r hr' => ?_
  simp only [shiftRanges, List.mem_map] at hr'
  obtain ⟨r', hr'', rfl⟩ := hr'
  have := hr r' hr''
  simp only
  omega_arith

/-- The exponentiation's ranges miss the array `j`. -/
theorem crtExpRanges_off {w j : Nat} (hj : j < 8) (h1 : aAcc ≠ j) (h2 : aTmp ≠ j) (h3 : aY ≠ j)
    (h4 : Crt.aT ≠ j) : ∀ r ∈ CrtWindowFive.crtExpRanges w,
      r.1 + r.2 ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ r.1 := by
  simp only [CrtWindowFive.crtExpRanges, crtWinRanges, List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, Or.inr (slot_le hj), slot_sep h1, slot_sep h2, slot_sep h3, slot_sep h4,
    ?_, ?_, ?_, ?_, ?_, List.forall_mem_nil _⟩ <;> refine Or.inl (hdr_lt_slot w j ?_) <;> decide

/-- The exponentiation's ranges miss the modulus and the number 1. -/
theorem crtExpRanges_off_nOne (w : Nat) : ∀ r ∈ CrtWindowFive.crtExpRanges w,
    (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
      (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1) := fun r hr =>
  ⟨crtExpRanges_off (by decide) (by decide) (by decide) (by decide) (by decide) r hr,
    crtExpRanges_off (by decide) (by decide) (by decide) (by decide) (by decide) r hr⟩

/-- The exponentiation's ranges miss `aX`. -/
theorem crtExpRanges_off_x (w : Nat) : ∀ r ∈ CrtWindowFive.crtExpRanges w,
    slot w aX + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aX := fun r hr =>
  (crtExpRanges_off (j := aX) (by decide) (by decide) (by decide) (by decide) (by decide) r hr).symm.imp_left
    fun h => Nat.le_trans (Nat.add_le_add_left (by omega_using []) _) h

theorem powRanges_x (w : Nat) : (slot w aX, 8 * (w + 2)) ∈ powRanges w := .head _
theorem powRanges_r2 (w : Nat) : (slot w aR2, 8 * (w + 2)) ∈ powRanges w := .tail _ (.head _)
theorem powRanges_xm (w : Nat) : (slot w aXm, 8 * (w + 2)) ∈ powRanges w := .tail _ (.tail _ (.head _))
theorem powRanges_acc (w : Nat) : (slot w aAcc, 8 * (w + 2)) ∈ powRanges w :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
theorem powRanges_tmp (w : Nat) : (slot w aTmp, 8 * (w + 2)) ∈ powRanges w :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
theorem powRanges_y (w : Nat) : (slot w aY, 8 * (w + 2)) ∈ powRanges w :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))

/-- The ranges `pow` changes before the exponentiation. -/
theorem powRanges_pre (w : Nat) : ∀ r ∈ ([(slot w aXm, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aY, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
    [(slot w aX, 8 * (w + 2))] ++ [(slot w aR2, 8 * (w + 2))]), r ∈ powRanges w := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [powRanges_xm w, powRanges_acc w, powRanges_tmp w, powRanges_y w, powRanges_acc w, powRanges_tmp w,
    powRanges_xm w, powRanges_x w, powRanges_r2 w]

/-- The ranges a Montgomery multiplication into `aY` changes. -/
theorem powRanges_mm (w : Nat) : ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aY, 8 * (w + 2))], r ∈ powRanges w := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [powRanges_acc w, powRanges_tmp w, powRanges_y w]

theorem pow_ok (W : Window) (M : Mont) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (S : Selector) (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow W.code S.code M.mm bp bl ep el)) s fun t => ModCtx t B Z o w mi X ∧
      wv t.mem (off B o) (slot w aY) w = Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X ∧
      Frm (off B o) (powRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw2 := hc.w2
  have hw28 := hc.w28
  have hn := hc.sub.scr.nowrap
  have hGn : (off B o).toNat + slot w 8 ≤ 2 ^ 64 := hc.sub.good.scr.nowrap
  have hlo := hc.sub.lo
  have hwide := hc.wide
  obtain hR : Nat.Coprime (2 ^ (64 * w)) X := VG.Proof.Bignum.coprime_pow2 hc.odd _
  obtain hX0 : 0 < X := by have := hc.x1; omega_arith
  obtain h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  obtain sXa := slot_le (w := w) (show aX < 8 by decide)
  obtain sR := slot_le (w := w) (show aR2 < 8 by decide)
  obtain sXm := slot_le (w := w) (show aXm < 8 by decide)
  obtain sY := slot_le (w := w) (show aY < 8 by decide)
  -- Arrays of the steps' ranges, all at least `8 * 17` and below `slot w 8`.
  obtain hA : ∀ j < 8, 8 * 17 ≤ slot w j := fun j hj => by have := hdr_lt_slot w j (show 31 < 32 by decide); omega_arith
  unfold pow
  simp only [List.append_assoc]
  -- The base into `aXm`.
  refine wp_seqs_append (by simp [loadArr]) (by simp) (WP.mono (primeLoad_ok hc.sub hw2 (Nat.le_refl _) (by omega_arith)
    (show aXm < 8 by decide) hbp hbl hpb hlb hsb hb1 (by omega_arith) hb2) fun s₁ ⟨hs₁, hb₁, ho₁, k₁⟩ => ?_)
  obtain f₁ : Frm (off B o) [(slot w aXm, 8 * (w + 2))] s.mem s₁.mem := Frm.of_outside ho₁ (by simp)
  obtain hv₁ : XVals s₁ B o w mi X := hc.xv.of_frmA hGn (by omega_arith) f₁ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  obtain hr2₁ : wv s₁.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) (show aR2 ≠ aXm by decide); omega_arith) (by omega_arith)
  have hg₁ := hs₁.good
  have hinv₁ := hv₁.inv
  -- `Y := R` (`R² · 1`).
  simp only [List.cons_append, List.nil_append]
  refine wp_seqs_cons (by simp) (WP.mono (M.mm_ok hg₁ (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv₁
    (by rw [hv₁.one, hv₁.n]; exact hc.x1)) fun s₂ ⟨hg₂, hYl₂, hYv₂, ha₂, k₂⟩ => ?_)
  simp only [hv₁.n, hv₁.one, Nat.mul_one] at hYl₂ hYv₂
  obtain f₂ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]
      s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp)
  obtain rng₂ : ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))],
      8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
  obtain hs₂ := hs₁.of_frm f₂ rng₂ k₂.wr (k₂.gpr .x0 (by decide))
  obtain hv₂ := hv₁.of_frmA hGn (by omega_arith) f₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  obtain nY : ∀ {j}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aY → wv s₂.mem (off B o) (slot w j) w = wv s₁.mem (off B o) (slot w j) w :=
    fun hj h1 h2 h3 => ha₂.wv_of_not_mem hj (by simp [h1, h2, h3]) hGn
  obtain hR2₂ : wv s₂.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [nY (by decide) (by decide) (by decide) (by decide), hr2₁]
  obtain hXm₂ : wv s₂.mem (off B o) (slot w aXm) w = Spec.Rsa.os2ip bb := by
    rw [nY (by decide) (by decide) (by decide) (by decide), hb₁]
  obtain hYR : wv s₂.mem (off B o) (slot w aY) w % X = 2 ^ (64 * w) % X := by
    apply mont_cancel hR
    rw [hYv₂, hr2₁, hc.r2]
  -- `Xm := b R`.
  refine wp_seqs_cons (by simp) (WP.mono (M.mm_ok hs₂.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aXm) (a := aXm)
    (b := aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv₂.inv
    (by rw [hR2₂, hv₂.n]; exact hc.r2l)) fun s₃ ⟨_, hXl₃, hXv₃, ha₃, k₃⟩ => ?_)
  simp only [hv₂.n, hXm₂, hR2₂] at hXv₃ hXl₃
  obtain f₃ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s₂.mem s₃.mem := Frm.of_arrays ha₃ (by simp)
  obtain hs₃ := hs₂.of_frm f₃ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩
    · exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₃.wr (k₃.gpr .x0 (by decide))
  obtain hv₃ := hv₂.of_frmA hGn (by omega_arith) f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  obtain nXm : ∀ {j}, j < 8 → j ≠ aAcc → j ≠ aTmp → j ≠ aXm →
      wv s₃.mem (off B o) (slot w j) w = wv s₂.mem (off B o) (slot w j) w :=
    fun hj h1 h2 h3 => ha₃.wv_of_not_mem hj (by simp [h1, h2, h3]) hGn
  obtain hXb : wv s₃.mem (off B o) (slot w aXm) w % X = Spec.Rsa.os2ip bb * 2 ^ (64 * w) % X := by
    apply mont_cancel hR
    rw [hXv₃, Nat.mul_mod, hc.r2, ← Nat.mul_mod, Nat.mul_assoc]
  -- `aX := R²`, `aXc := b R`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hs₃.good (Nat.le_refl _) (by omega_arith)
    (by omega_arith) (show aX < 8 by decide) (show aR2 < 8 by decide) (by decide)) fun s₄ ⟨hX₄, ho₄, k₄⟩ => ?_)
  obtain f₄ : Frm (off B o) [(slot w aX, 8 * (w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain hs₄ := hs₃.of_frm f₄ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₄.wr (k₄.gpr .x0 (by decide))
  obtain hv₄ := hv₃.of_frmA hGn (by omega_arith) f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  obtain n₄ : ∀ {j}, j < 8 → j ≠ aX → wv s₄.mem (off B o) (slot w j) w = wv s₃.mem (off B o) (slot w j) w :=
    fun hj h1 => f₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) h1; omega_arith)
      (by have := slot_le (w := w) hj; omega_arith)
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hs₄.good (Nat.le_refl _) (by omega_arith)
    (by omega_arith) (show Crt.aXc < 8 by decide) (show aXm < 8 by decide) (by decide)) fun s₅ ⟨hX₅, ho₅, k₅⟩ => ?_)
  have eXc : Crt.aXc = aR2 := rfl
  rw [eXc] at hX₅ ho₅
  obtain f₅ : Frm (off B o) [(slot w aR2, 8 * (w + 2))] s₄.mem s₅.mem :=
    Frm.of_outside (ho₅.mono (o' := slot w aR2) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain hs₅ := hs₄.of_frm f₅ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₅.wr (k₅.gpr .x0 (by decide))
  obtain hv₅ := hv₄.of_frmA hGn (by omega_arith) f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  obtain n₅ : ∀ {j}, j < 8 → j ≠ aR2 → wv s₅.mem (off B o) (slot w j) w = wv s₄.mem (off B o) (slot w j) w :=
    fun hj h1 => f₅.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) h1; omega_arith)
      (by have := slot_le (w := w) hj; omega_arith)
  -- Values before the exponentiation.
  obtain hXc₅ : wv s₅.mem (off B o) (slot w Crt.aXc) w = wv s₃.mem (off B o) (slot w aXm) w := by
    rw [eXc, hX₅, n₄ (by decide) (by decide)]
  obtain hY₅ : wv s₅.mem (off B o) (slot w aY) w = wv s₂.mem (off B o) (slot w aY) w := by
    rw [n₅ (by decide) (by decide), n₄ (by decide) (by decide), nXm (by decide) (by decide) (by decide) (by decide)]
  obtain hXa₅ : wv s₅.mem (off B o) (slot w aX) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [n₅ (by decide) (by decide), hX₄, nXm (by decide) (by decide) (by decide) (by decide)]; exact hR2₂
  -- The exponentiation.
  obtain F₅ : Frm (off B o) ([(slot w aXm, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aY, 8 * (w + 2))] ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
      [(slot w aX, 8 * (w + 2))] ++ [(slot w aR2, 8 * (w + 2))]) s.mem s₅.mem :=
    (((f₁.append f₂).append f₃).append f₄).append f₅
  obtain rF₅ := powRanges_pre w
  obtain ⟨hb₅, hi₅⟩ := child_frm hc.sub hwide F₅ (fun r hr => (powRanges_ok w r (rF₅ r hr)).2)
  obtain K₅ := keep_trans (keep_trans (keep_trans (keep_trans k₁ k₂) k₃) k₄) k₅
  refine wp_seqs_cons (by simp) (WP.mono (expLoop_ok W M S (Q := True) (x := Spec.Rsa.os2ip bb) (ep := pe) (eb := eb) hs₅ hwide hw2
    (Nat.le_refl _) (by omega_arith) hv₅.n hv₅.inv hc.odd (by rw [hXc₅]; exact hXl₃) (fun _ => by rw [hXc₅]; exact hXb)
    (by rw [hY₅]; exact hYl₂) (fun _ => by rw [hY₅]; exact hYR) hep hel (by rw [hb₅ _ hep]; exact hpe)
    (by rw [hb₅ _ hel]; exact hle) he1 he2 (hse.congrK hi₅ K₅)) fun s₆ ⟨hs₆, hYl₆, hYv₆, f₆, k₆⟩ => ?_)
  obtain hYv₆' := hYv₆ trivial
  obtain hv₆ := hv₅.of_frmA hGn (by omega_arith) f₆ (crtExpRanges_off_nOne w)
  obtain hX₆ : wv s₆.mem (off B o) (slot w aX) w = wv s₅.mem (off B o) (slot w aX) w :=
    f₆.wv_eq (crtExpRanges_off_x w) (by omega_arith)
  -- `Y := Y R⁻¹`, out of Montgomery form.
  refine wp_seqs_cons (by simp [copyArr]) (WP.mono (M.mm_ok hs₆.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aY) (a := aY)
    (b := aOne) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv₆.inv
    (by rw [hv₆.one, hv₆.n]; exact hc.x1)) fun s₇ ⟨_, hYl₇, hYv₇, ha₇, k₇⟩ => ?_)
  simp only [hv₆.n, hv₆.one, Nat.mul_one] at hYl₇ hYv₇
  obtain hY₇ : wv s₇.mem (off B o) (slot w aY) w = Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X := by
    rw [← Nat.mod_eq_of_lt hYl₇]
    exact mont_cancel hR (by rw [hYv₇, hYv₆'])
  obtain f₇ : Frm (off B o) [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]
      s₆.mem s₇.mem := Frm.of_arrays ha₇ (by simp)
  obtain hs₇ := hs₆.of_frm f₇ rng₂ k₇.wr (k₇.gpr .x0 (by decide))
  obtain hv₇ := hv₆.of_frmA hGn (by omega_arith) f₇ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact arr_off w (by decide) (by decide))
  obtain hX₇ : wv s₇.mem (off B o) (slot w aX) w = wv s.mem (off B o) (slot w aR2) w := by
    rw [ha₇.wv_of_not_mem (by decide) (by decide) hGn, hX₆, hXa₅]
  -- `R²` back.
  refine WP.mono (copyArr_ok hs₇.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aR2 < 8 by decide)
    (show aX < 8 by decide) (by decide)) fun t ⟨hR₈, ho₈, k₈⟩ => ?_
  obtain f₈ : Frm (off B o) [(slot w aR2, 8 * (w + 2))] s₇.mem t.mem :=
    Frm.of_outside (ho₈.mono (o' := slot w aR2) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain hs₈ := hs₇.of_frm f₈ (by
    simp only [List.mem_singleton, forall_eq]; exact ⟨hA _ (by decide), slot_le (by decide)⟩) k₈.wr (k₈.gpr .x0 (by decide))
  obtain hv₈ := hv₇.of_frmA hGn (by omega_arith) f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact arr_off w (by decide) (by decide))
  obtain hY₈ : wv t.mem (off B o) (slot w aY) w = wv s₇.mem (off B o) (slot w aY) w :=
    f₈.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; have := slot_sep (w := w) (show aY ≠ aR2 by decide); omega_arith)
      (by omega_arith)
  refine ⟨⟨hs₈, hv₈, by rw [hR₈, hX₇]; exact hc.r2l, by rw [hR₈, hX₇]; exact hc.r2, hc.odd, hc.x1, hwide, hw2, hw28⟩,
    by rw [hY₈, hY₇], ?_, ?_⟩
  · have g₆ : Frm (off B o) (powRanges w) s₅.mem s₆.mem := f₆.mono fun r hr => by
      simp only [powRanges, List.mem_cons]; exact Or.inr (Or.inr (Or.inr hr))
    obtain g₇ : Frm (off B o) (powRanges w) s₆.mem s₇.mem := f₇.mono (powRanges_mm w)
    obtain g₈ : Frm (off B o) (powRanges w) s₇.mem t.mem := f₈.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact powRanges_r2 w
    exact (((F₅.mono rF₅).trans g₆).trans g₇).trans g₈
  · exact keep_trans (keep_trans (keep_trans K₅ k₆) k₇) k₈

end VG.Proof.Ffdh.AArch64

end

end

/-!
# FFDH on AArch64: the front of the domain operations

From the outer header with the domain's pointer and p's length: the check of
p (`domHead_ok`); the outer workspace and the inner one for p, with p, `-p⁻¹`
and the number 1 (`setup_ok`); `R² mod p` (`r2_ctx`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (wsEnd wsNew loadArr leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- Header slots of the outer workspace with given values. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

theorem Slots.frm {m m' : Mem} {B : Addr} {L : List (Nat × BitVec 64)} {rs : List (Nat × Nat)} (h : Slots m B L)
    (hf : Frm B rs m m') (hr : ∀ p ∈ L, ∀ r ∈ rs, 8 * p.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * p.1)
    (hL : ∀ p ∈ L, p.1 < 32) : Slots m' B L := fun p hp => by
  rw [hf.word_eq (hr p hp) (by have := hL p hp; omega_arith)]; exact h p hp

/-! ## The check of p -/

/-- `domHead`'s loads and stores before the check of p. -/
theorem domHead1_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) (hD : word s.mem B (8 * sDom) = dp)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) :
    WP isa (.block [ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ]) s
      fun t => (t.gpr .x2 = dp ∧ t.gpr .x3 = BitVec.ofNat 64 k ∧
        t.mem = (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)).writeW (off B (8 * sQ))
          (dp + BitVec.ofNat 64 k + BitVec.ofNat 64 k)) ∧ Keep [.x2, .x3, .x4] s t := by
  have hn := hs.nowrap
  have eG : sG = 27 := rfl
  have eQ : sQ = 28 := rfl
  have eD : sDom = 16 := rfl
  have eK : sK = 18 := rfl
  refine WP.keep [.x2, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, hdr_enc (show sDom < 32 by decide), hdr_enc (show sK < 32 by decide), hdr_enc (show sG < 32 by decide),
    hdr_enc (show sQ < 32 by decide), hs.ld (d := 8 * sDom) (by omega_arith), hs.ld (d := 8 * sK) (by omega_arith),
    hs.st (d := 8 * sG) (by omega_arith), hs.st (d := 8 * sQ) (by omega_arith), hD, hK]

/-- `domHead`: g's and q's pointers into their slots, and `x9 :=` whether p (the
first `p_len` octets of the domain) is a valid modulus. -/
theorem domHead_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) :
    WP isa (.block domHead) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k).toNat ∧
      word t.mem B (8 * sG) = dp + BitVec.ofNat 64 k ∧ word t.mem B (8 * sQ) = dp + BitVec.ofNat 64 (2 * k) ∧
      Frm B [(8 * sG, 8), (8 * sQ, 8)] s.mem t.mem ∧ t.gpr .x0 = B ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t := by
  have hn := hs.nowrap
  have eG : sG = 27 := rfl
  have eQ : sQ = 28 := rfl
  have eD : sDom = 16 := rfl
  have eK : sK = 18 := rfl
  unfold domHead
  rw [show ([ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ] ++ invalid) =
    [ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ] ++ invalid from rfl,
    WP.block_append_iff]
  refine WP.mono (domHead1_ok hs h0 hZ hD hK) fun t₁ ⟨⟨h2, h3, hm₁⟩, k₁⟩ => ?_
  obtain o₁ := writeW_outside s.mem B (d := 8 * sG) (dp + BitVec.ofNat 64 k) (by omega_arith)
  obtain o₂ := writeW_outside (s.mem.writeW (off B (8 * sG)) (dp + BitVec.ofNat 64 k)) B (d := 8 * sQ)
    (dp + BitVec.ofNat 64 k + BitVec.ofNat 64 k) (by omega_arith)
  obtain hsrc₁ : Src t₁ B Z dp pb := hsrc.congr (fun x hx => by
      rw [hm₁, o₂ x (Or.inr (by omega_arith)), o₁ x (Or.inr (by omega_arith))]) k₁.rd k₁.wr
  refine WP.mono (invalid_ok h2 h3 hk1 hk2 hl (fun i hi => hsrc₁.rd i (by omega_arith)) (fun i hi => hsrc₁.val i _))
    fun t ⟨h9, hm, k₂⟩ => ⟨h9, ?_, ?_, ?_, (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0),
      (k₁.trans k₂).mono (by decide)⟩
  · rw [hm, hm₁, o₂.word (by omega_arith) (by omega_arith)]; exact word_writeW_self _ _ _ _
  · rw [hm, hm₁, word_writeW_self, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  · intro x hx
    rw [hm, hm₁, o₂ x (hx (8 * sQ, 8) (by simp)), o₁ x (hx (8 * sG, 8) (by simp))]

/-! ## The workspaces -/

/-- What `head` and `pSetup` change in the outer workspace. -/
def setupR (w : Nat) : List (Nat × Nat) := [(8 * sW, 8), (8 * sArr 0, 64), (8 * sWs, 8), (inner w, slot w 8)]

/-- A header slot that `head` and `pSetup` don't write is outside `setupR`. -/
theorem setupR_word (w : Nat) {i : Nat} (hi : i < 32) (h1 : i ≠ sW) (h2 : i ≠ sWs) (h3 : i < sArr 0 ∨ sArr 0 + 8 ≤ i) :
    ∀ r ∈ setupR w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  obtain h8 := hdr_lt_slot w 8 hi
  simp only [setupR, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sW sWs sArr sFn at *
  exact ⟨by omega_using [h1], by omega_using [h3], by omega_using [h2], Or.inl h8⟩

/-- `setupR` within a working space with room for the inner workspace. -/
theorem setupR_le (w : Nat) {Z : Nat} (h : inner w + slot w 8 ≤ Z) : ∀ r ∈ setupR w, r.1 + r.2 ≤ Z := by
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [setupR, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  unfold sW sWs sArr sFn at *
  exact ⟨by omega_using [h, h8], by omega_using [h, h8], by omega_using [h, h8], h⟩

theorem wsWords_k {k : Nat} (hk : 16 ≤ k) : wsWords k = (k + 7) / 8 := by unfold wsWords; omega_arith

/-- The workspaces' room in the working space of `16 k + 32` words. -/
theorem room_k {k Z : Nat} (hk : 64 ≤ k) (hZ : 128 * k + 256 ≤ Z) :
    inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 + tabBytes32 ((k + 7) / 8) ≤ Z := by
  simp only [inner, slot, hdrBytes, tabBytes32]
  generalize hw : (k + 7) / 8 = w
  obtain h8 : 8 * w ≤ k + 7 := by omega_arith
  obtain e : 256 + 8 * (8 * (w + 2)) + (256 + 8 * (8 * (w + 2))) + 32 * (8 * (w + 2)) = 384 * w + 1280 := by omega_arith
  rw [e]
  omega_arith

/-- `head`, then the inner workspace for p, entered, with p, `-p⁻¹` and the
number 1. -/
theorem setup_ok {s : State} {B : Addr} {Z k : Nat} {dp : Addr} {pb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024) (hZ : 128 * k + 256 ≤ Z)
    (hD : word s.mem B (8 * sDom) = dp) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hsrc : Src s B Z dp pb) (hl : pb.length = k) (hodd : Spec.Rsa.os2ip pb % 2 = 1) :
    WP isa (seqs (([.block head] : List (Prog isa)) ++ pSetup)) s fun t => ∃ mi,
      SubCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi ∧
      XVals t B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      word t.mem B (8 * sWs) = off B (inner ((k + 7) / 8)) ∧
      Frm B (setupR ((k + 7) / 8)) s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  obtain hroom := room_k hk1 hZ
  obtain eW : wsWords k = (k + 7) / 8 := wsWords_k (by omega_arith)
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eW6 : sW = 6 := rfl
  have eA8 : sArr 0 = 8 := rfl
  have eWs : sWs = 29 := rfl
  obtain hi8 : 8 * 32 ≤ inner ((k + 7) / 8) := by simp only [inner, slot, hdrBytes]; omega_arith
  obtain hiZ : inner ((k + 7) / 8) + slot ((k + 7) / 8) 8 ≤ Z := by unfold tabBytes32 at hroom; omega_arith
  refine wp_seqs_cons (by simp [pSetup]) (WP.mono (head_ok hs h0 (by unfold inner at hroom; omega_arith) (by omega_arith) hK)
    fun s₁ ⟨h12, hW, hA, f₁, k₁⟩ => ?_)
  obtain hO : Outer s₁ B Z ((k + 7) / 8) :=
    ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans h0, hW, hA, hroom, by omega_arith, by omega_arith⟩
  obtain hr₁ : ∀ i < 32, i ≠ sW → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) → word s₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi h1 h2 => f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  obtain hK₁ : word s₁.mem B (8 * sK) = BitVec.ofNat 64 k := by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hK
  obtain hD₁ : word s₁.mem B (8 * sDom) = dp := by rw [hr₁ _ (by decide) (by decide) (by decide)]; exact hD
  obtain hsrc₁ : Src s₁ B Z dp pb := hsrc.congrK (InScr.of_frm f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) k₁
  unfold pSetup
  refine wp_seqs_cons (by simp [modSetup, loadArr]) (WP.mono (wsSetup_ok (len := k) hO (by decide) (by decide)
    (by rw [hK₁]) (by omega_arith) (by omega_arith)) fun s₂ ⟨hc₂, hWs₂, f₂, k₂⟩ => ?_)
  rw [eW] at hc₂
  obtain hb₂ : ∀ i < 32, i ≠ sWs → word s₂.mem B (8 * i) = word s₁.mem B (8 * i) := fun i hi hne =>
    f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  obtain i₂ : InScr B Z s₁.mem s₂.mem := InScr.of_frm f₂ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  refine WP.mono (modSetup_ok hc₂ (by omega_arith) (Nat.le_refl _) (by omega_arith) (show sDom < 32 by decide)
    (show sK < 32 by decide) (by rw [hb₂ _ (by decide) (by decide)]; exact hD₁)
    (by rw [hb₂ _ (by decide) (by decide), hl]; exact hK₁) (hsrc₁.congrK i₂ k₂) (by omega_arith) (by rw [hl]) hodd)
    fun t ⟨mi, hc, hv, f₃, k₃⟩ => ⟨mi, hc, hv, ?_, ?_, ?_⟩
  · have hr₃ : ∀ r ∈ [(slot ((k + 7) / 8) aN, 8 * ((k + 7) / 8 + 2)), (slot ((k + 7) / 8) aOne, 8 * ((k + 7) / 8 + 2)),
        (8 * sMinv, 8)], r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact slot_le (by decide)
      · exact slot_le (by decide)
      · have := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide); simp only; omega_arith
    rw [f₃.word_below hr₃ (by omega_arith) (by omega_arith) (by omega_arith)]; exact hWs₂
  · intro x hx
    obtain hr₃ : ∀ r ∈ [(slot ((k + 7) / 8) aN, 8 * ((k + 7) / 8 + 2)), (slot ((k + 7) / 8) aOne, 8 * ((k + 7) / 8 + 2)),
        (8 * sMinv, 8)], inner ((k + 7) / 8) + r.1 + r.2 ≤ 2 ^ 64 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · have := slot_le (w := (k + 7) / 8) (show aN < 8 by decide); simp only; omega_arith
      · have := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide); simp only; omega_arith
      · have := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide); simp only; omega_arith
    obtain g₃ := f₃.rebase (by omega_arith) hr₃
    rw [g₃ x (fun r hr => by
      simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain hx' := hx (inner ((k + 7) / 8), slot ((k + 7) / 8) 8) (by simp [setupR])
      obtain s1 := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
      obtain s2 := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide)
      obtain s3 := hdr_lt_slot ((k + 7) / 8) 8 (show sMinv < 32 by decide)
      rcases hr with rfl | rfl | rfl <;> simp only at hx' ⊢ <;> omega_arith),
      f₂ x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx (8 * sWs, 8) (by simp [setupR])
        · have hx' := hx (inner ((k + 7) / 8), slot ((k + 7) / 8) 8) (by simp [setupR])
          simp only at hx' ⊢; omega_arith),
      f₁ x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx (8 * sW, 8) (by simp [setupR])
        · exact hx (8 * sArr 0, 64) (by simp [setupR]))]
  · exact keep_trans ((k₁.trans k₂).mono (by decide)) (k₃.mono (by decide))

/-- `R² mod p` in the inner workspace for a valid modulus p. -/
theorem r2_ctx (M : Mont) {t : State} {B : Addr} {Z k : Nat} {mi : BitVec 64} {pb : List Byte}
    (hc : SubCtx t B Z (inner ((k + 7) / 8)) ((k + 7) / 8) ((k + 7) / 8) mi)
    (hv : XVals t B (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb))
    (hval : Spec.Rsa.modulusValid (Spec.Rsa.os2ip pb) k = true) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hZ : 128 * k + 256 ≤ Z) :
    WP isa (seqs (r2Steps M.mm)) t fun t' =>
      ModCtx t' B Z (inner ((k + 7) / 8)) ((k + 7) / 8) mi (Spec.Rsa.os2ip pb) ∧
      Frm (off B (inner ((k + 7) / 8))) (r2Ranges ((k + 7) / 8)) t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨hodd, h1, hlo⟩ := valid_facts hval hk1
  obtain hroom := room_k hk1 hZ
  have hGn := hc.good.scr.nowrap
  refine WP.mono (r2_ok M hc.good (Nat.le_refl _) (by omega_arith) (by omega_arith) hv.n hv.inv hodd hlo)
    fun t' ⟨hg', hlt, hr, f, kk⟩ => ?_
  obtain hr' : ∀ r ∈ r2Ranges ((k + 7) / 8), 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := fun r hr' => by
    refine ⟨?_, r2Ranges_le ((k + 7) / 8) r hr'⟩
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl <;> simp only [slot, hdrBytes, aAcc, aTmp, aR2, sCnt, sFn] <;> omega_arith
  refine ⟨⟨hc.of_frm f hr' kk.wr (kk.gpr .x0 (by decide)), hv.of_frmA hGn (by omega_arith) f (fun r hr'' => ⟨?_, ?_⟩),
    hlt, hr, hodd, h1, by unfold inner at hroom ⊢; omega_arith, by omega_arith, by omega_arith⟩, f, kk⟩
  · exact r2Ranges_arr _ (j := aN) (by decide) (by decide) (by decide) r hr'' |>.symm
  · exact r2Ranges_arr _ (j := aOne) (by decide) (by decide) (by decide) r hr'' |>.symm

/-! ## Octets outside the working space -/

theorem src_slice {s : State} {B : Addr} {Z : Nat} {p : Addr} {m : Mem} {n : Nat} (h : Src s B Z p (Spec.Rsa.bytesAt m p n))
    {off len : Nat} (hle : off + len ≤ n) :
    Src s B Z (p + BitVec.ofNat 64 off) (Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 off) len) := by
  obtain e : ∀ i, p + BitVec.ofNat 64 off + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (off + i) := fun i => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    rw [e]; exact h.rd (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    have := h.val (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] at this ⊢
    rw [e, this]
  · simp only [VG.Proof.Bignum.bytesAt_length] at hi
    rw [e]; exact h.out (off + i) (by simp only [VG.Proof.Bignum.bytesAt_length]; omega_arith)

/-! ## Moving between the workspaces -/

/-- `SubCtx` but for `x0`: the memory and permissions of the inner workspace,
whichever workspace the code is in. -/
structure SubMem (t : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) : Prop where
  scr : Scr t B Z
  hdr : Hdr t.mem (off B o) wx minv
  link : word t.mem (off B o) (8 * Crt.sLink) = B
  nw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  narr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  lo : slot w 8 ≤ o
  hi : o + slot wx 8 + tabBytes wx ≤ Z

theorem _root_.VG.Proof.Bignum.AArch64.SubCtx.toMem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (h : SubCtx t B Z o w wx mi) : SubMem t B Z o w wx mi :=
  ⟨h.scr, h.hdr, h.link, h.nw, h.narr, h.lo, h.hi⟩

theorem SubMem.ctx {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (h : SubMem t B Z o w wx mi)
    (h0 : t.gpr .x0 = off B o) : SubCtx t B Z o w wx mi :=
  ⟨h.scr, h0, h.hdr, h.link, h.nw, h.narr, h.lo, h.hi⟩

theorem SubMem.congr {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (h : SubMem s B Z o w wx mi)
    (hm : t.mem = s.mem) (hwr : t.wr = s.wr) : SubMem t B Z o w wx mi :=
  ⟨h.scr.congr hwr, by rw [hm]; exact h.hdr, by rw [hm]; exact h.link, by rw [hm]; exact h.nw,
    by rw [hm]; exact h.narr, h.lo, h.hi⟩

/-- `SubMem` after a change of the outer header's own slots. -/
theorem SubMem.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (hc : SubMem s B Z o w wx mi) (hf : Frm B rs s.mem t.mem) (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256)
    (hwr : t.wr = s.wr) : SubMem t B Z o w wx mi := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  obtain h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  obtain hc' : ∀ d, o ≤ d → d + 8 ≤ Z → word t.mem B d = word s.mem B d := fun d h1 h2 =>
    hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)
  obtain hp : ∀ i < 16, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_arith)) (by omega_arith)
  obtain hh : ∀ i < 32, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' => by
    rw [word_off, word_off]; exact hc' _ (by omega_arith) (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  exact ⟨hc.scr.congr hwr,
    ⟨(hh _ (by decide)).trans hc.hdr.hw, (hh _ (by decide)).trans hc.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_arith)).trans (hc.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans hc.link, (hp _ (by decide)).trans hc.nw,
    fun j hj => (hp _ (by unfold sArr; omega_arith)).trans (hc.narr j hj), hc.lo, hc.hi⟩

/-- The outer workspace, from the inner one's memory. -/
theorem Outer.of_mem {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubMem t B Z o w wx mi)
    (h0 : t.gpr .x0 = B) (hroom : inner w + slot w 8 + tabBytes32 w ≤ Z) (hw2 : 2 ≤ w) (hw : w < 2 ^ 28) :
    Outer t B Z w :=
  ⟨hc.scr, h0, hc.nw, hc.narr, hroom, hw2, hw⟩

/-- From the inner workspace, back to the outer one, and `x3 := domain_len − 2 p_len`. -/
theorem leaveQ_ok {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {dl k : Nat}
    (hc : SubCtx t B Z o w wx mi) (hdl : word t.mem B (8 * sDomLen) = BitVec.ofNat 64 dl)
    (hk : word t.mem B (8 * sK) = BitVec.ofNat 64 k) (hdk : 2 * k ≤ dl) :
    WP isa (.block (leave :: qTest)) t fun t' => (t'.gpr .x0 = B ∧ t'.gpr .x3 = BitVec.ofNat 64 (dl - 2 * k) ∧
      t'.mem = t.mem) ∧ Keep [.x0, .x3, .x4] t t' := by
  refine WP.keep [.x0, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  unfold leave qTest
  brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show sDomLen < 32 by decide),
    hdr_enc (show sK < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), off_off, hc.link',
    hc.ldn (show sDomLen < 32 by decide), hc.ldn (show sK < 32 by decide), hdl, hk]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- From the inner workspace, back to the outer one. -/
theorem leave_ok {t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubCtx t B Z o w wx mi) :
    WP isa (.block [leave]) t fun t' => (t'.gpr .x0 = B ∧ t'.mem = t.mem) ∧ Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by decide) (by decide) (by decide +kernel)
  unfold leave
  brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), off_off, hc.link']

/-- `-m⁻¹` of the same odd modulus is the same. -/
theorem xvals_minv {s t : State} {B : Addr} {o w : Nat} {mi₁ mi₂ : BitVec 64} {X : Nat} (hw : 1 ≤ w)
    (hodd : X % 2 = 1) (h₁ : XVals s B o w mi₁ X) (h₂ : XVals t B o w mi₂ X) : mi₁ = mi₂ := by
  obtain e : ∀ {u : State} {mi : BitVec 64}, XVals u B o w mi X → ((X % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 :=
    fun h => by have hi := h.inv; rwa [← wv_mod64 _ _ _ hw, h.n] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hodd) (e h₁) (e h₂)

/-- Into the inner workspace. -/
theorem enter_ok {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w)
    (hWs : word t.mem B (8 * sWs) = off B (inner w)) :
    WP isa (.block [enter]) t fun t' => (t'.gpr .x0 = off B (inner w) ∧ t'.mem = t.mem) ∧ Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by decide) (by decide) (by decide +kernel)
  unfold enter
  brun [h.x0, hdr_enc (show sWs < 32 by decide), h.ld (show sWs < 32 by decide), hWs]

/-- Return `r`. -/
theorem ret_ok (t : State) {r : Nat} (hr : r < 65536) :
    WP isa (VG.Impl.Ffdh.AArch64.Domain.ret r) t fun t' => (t'.gpr .x0 = BitVec.ofNat 64 r ∧ t'.mem = t.mem) ∧
      Keep [.x0] t t' := by
  refine WP.keep [.x0] ?_ (by unfold VG.Impl.Ffdh.AArch64.Domain.ret; cases r <;> rfl) rfl
    (by unfold VG.Impl.Ffdh.AArch64.Domain.ret; rfl)
  unfold VG.Impl.Ffdh.AArch64.Domain.ret movi
  brun
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem setWidth32_bit (p : Prop) [Decidable p] :
    ((if p then (1 : BitVec 64) else 0).setWidth 32).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem setWidth32_ofNat {r : Nat} (hr : r < 2 ^ 32) : ((BitVec.ofNat 64 r).setWidth 32).toNat = r := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith

/-- A branch on a register holding 0 or 1. -/
theorem wp_ite_bit {th el : Prog isa} {s : State} {Q : State → Prop} {r : Reg} {P : Prop} [Decidable P]
    (h : s.gpr r = if P then 1 else 0) (ht : ¬ P → WP isa th s Q) (he : P → WP isa el s Q) :
    WP isa (.ite (.zero .x r) th el) s Q := by
  refine WP.ite (!decide P) (by rw [VG.Proof.MlKem.AArch64.eval_zero, h]; by_cases hp : P <;> simp [hp]) (fun hb => ?_)
    (fun hb => ?_)
  · exact ht (by simpa using hb)
  · exact he (by simpa using hb)

/-- `XVals` after a change of the outer header's own slots. -/
theorem _root_.VG.Proof.Bignum.AArch64.XVals.of_parent {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (hc : SubMem s B Z o w wx mi) (h : XVals s B o wx mi X) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 256) : XVals t B o wx mi X := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  obtain h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_arith
  obtain sN := slot_le (w := wx) (show aN < 8 by decide)
  obtain sO := slot_le (w := wx) (show aOne < 8 by decide)
  obtain e : ∀ d k, d + 8 * k ≤ slot wx 8 → wv t.mem (off B o) d k = wv s.mem (off B o) d k := fun d k hd =>
    wv_congr fun i hi' => by
      rw [word_off, word_off]
      exact hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith)
  refine ⟨by rw [e _ _ (by omega_arith)]; exact h.n, ?_, by rw [e _ _ (by omega_arith)]; exact h.one⟩
  rw [word_off, hf.word_eq (fun r hr' => Or.inr (by have := hr r hr'; omega_arith)) (by omega_arith), ← word_off]
  exact h.inv

/-! ## A power compared with 1 -/

/-- `pow` then `isOne aY`: `x9 := b^e mod X = 1`. -/
theorem powOne_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64}
    {X : Nat} (hc : ModCtx s B Z o w mi X)
    {bp bl ep el : Nat} (hbp : bp < 32) (hbl : bl < 32) (hep : ep < 32) (hel : el < 32)
    {pb pe : Addr} {bb eb : List Byte}
    (hpb : word s.mem B (8 * bp) = pb) (hlb : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hsb : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hb2 : (bb.length + 7) / 8 ≤ w)
    (hpe : word s.mem B (8 * ep) = pe) (hle : word s.mem B (8 * el) = BitVec.ofNat 64 eb.length)
    (hse : Src s B Z pe eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (seqs (pow W.code S.code M.mm bp bl ep el ++ isOne aY)) s fun t => ModCtx t B Z o w mi X ∧
      t.gpr .x9 = bit (Spec.Rsa.os2ip bb ^ Spec.Rsa.os2ip eb % X = 1) ∧
      Frm (off B o) (powRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [pow, loadArr]) (by simp [isOne, eqArr]) (WP.mono (pow_ok W M S hc hbp hbl hep hel
    hpb hlb hsb hb1 hb2 hpe hle hse he1 he2) fun t₁ ⟨hc₁, hY, f₁, k₁⟩ => ?_)
  have hw2 := hc₁.w2
  have hw28 := hc₁.w28
  refine WP.mono (eqArr_ok hc₁.sub.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (show aY < 8 by decide)
    (show aOne < 8 by decide)) fun t ⟨h9, hm, k⟩ => ?_
  obtain hc' : ModCtx t B Z o w mi X := by
    obtain ⟨hs, hv, r2l, r2, hodd, hx1, hwide, -, -⟩ := hc₁
    have hn := hs.good.scr.nowrap
    obtain e : ∀ d n, wv t.mem (off B o) d n = wv t₁.mem (off B o) d n := fun d n => by rw [hm]
    exact ⟨⟨hs.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hs.x0, by rw [hm]; exact hs.hdr,
      by rw [hm]; exact hs.link, by rw [hm]; exact hs.nw, by rw [hm]; exact hs.narr, hs.lo, hs.hi⟩,
      ⟨by rw [e]; exact hv.n, by rw [hm]; exact hv.inv, by rw [e]; exact hv.one⟩,
      by rw [e]; exact r2l, by rw [e]; exact r2, hodd, hx1, hwide, hw2, hw28⟩
  refine ⟨hc', by rw [h9, hY, hc₁.xv.one], by rw [hm]; exact f₁, keep_trans k₁ k⟩

/-! ## Slices of sources -/

theorem _root_.VG.Proof.Bignum.AArch64.Src.take {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z ptr (bs.take n) :=
  ⟨fun i hi => h.rd i (by simp at hi; omega_arith), fun i hi => by rw [List.getElem_take]; exact h.val i _,
    fun i hi => h.out i (by simp at hi; omega_arith)⟩

theorem _root_.VG.Proof.Bignum.AArch64.Src.drop {t : State} {B : Addr} {Z : Nat} {ptr : Addr} {bs : List Byte}
    (h : Src t B Z ptr bs) (n : Nat) : Src t B Z (ptr + BitVec.ofNat 64 n) (bs.drop n) := by
  obtain e : ∀ i, ptr + BitVec.ofNat 64 n + BitVec.ofNat 64 i = ptr + BitVec.ofNat 64 (n + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [e]; exact h.rd _ (by simp at hi; omega_arith)
  · rw [e, List.getElem_drop]; exact h.val _ _
  · rw [e]; exact h.out _ (by simp at hi; omega_arith)

end VG.Proof.Ffdh.AArch64
