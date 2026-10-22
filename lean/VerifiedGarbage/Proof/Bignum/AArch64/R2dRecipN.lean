module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Recip

import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64: the reciprocal by Newton steps

`R2Div.recipN`: `recipGuess` leaves some guess of
`v = ⌊(2^128 - 1) / d⌋ - 2^64` in `x10`, of which nothing is proven but that
it is a word (`recipGuess_ok`); `recipDown` then lowers it while
`(2^64 + v) d ≥ 2^128` (`down_ok`, `downLoop_ok`), and `recipUp` raises it
while `(2^64 + v + 1) d < 2^128` (`up_ok`, `upLoop_ok`), which leaves the
largest `v` with `(2^64 + v) d < 2^128`: `v` itself (`r2dRecipN_ok`, with
`recip`'s statement, `r2dRecip_ok`), by `Recip.recip_exact`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div VG.Proof.Bignum VG.Proof.Bignum.Recip
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)

/-! ## The guess -/

/-- What a Newton step leaves in `x10`, from `v` in `x10` and `d` in `x5`. -/
def stepV (v d : BitVec 64) : BitVec 64 :=
  let e := (BitVec.ofNat 64 (v.toNat * d.toNat / 2 ^ 64) + d) ^^^ BitVec.allOnes 64
  v + (e + BitVec.ofNat 64 (e.toNat * v.toNat / 2 ^ 64))

/-- `n` Newton steps from `v`. -/
def stepsV (d : BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0, v => v
  | n + 1, v => stepsV d n (stepV v d)

/-- What `recipGuess` leaves in `x10`, for `d = m[w - 1]`. -/
def guessV (d : BitVec 64) : BitVec 64 := stepsV d 6 (d ^^^ BitVec.allOnes 64)

/-- A Newton step writes only `x2`, `x3` and `x10`. -/
theorem recipStep_ok (t : State) (h4 : t.gpr .x4 = BitVec.allOnes 64) :
    WP isa (.block recipStep) t fun t' => (t'.gpr .x10 = stepV (t.gpr .x10) (t.gpr .x5) ∧ t'.mem = t.mem) ∧
      Keep [.x2, .x3, .x10] t t' := by
  refine WP.keep [.x2, .x3, .x10] ?_ (by decide) rfl (by decide +kernel)
  brun [recipStep, h4]
  rfl

/-- `n` Newton steps. -/
theorem recipSteps_ok (n : Nat) (t : State) (h4 : t.gpr .x4 = BitVec.allOnes 64) :
    WP isa (.block (List.replicate n recipStep).flatten) t fun t' =>
      t'.gpr .x10 = stepsV (t.gpr .x5) n (t.gpr .x10) ∧ t'.mem = t.mem ∧ Keep [.x2, .x3, .x10] t t' := by
  induction n generalizing t with
  | zero => exact WP.block_nil ⟨rfl, rfl, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (recipStep_ok t h4) fun t₁ ⟨⟨h10, hm⟩, k⟩ => ?_
    refine WP.mono (ih t₁ ((k.gpr .x4 (by decide)).trans h4)) fun t' ⟨h10', hm', k'⟩ =>
      ⟨by rw [h10', h10, k.gpr .x5 (by decide)]; rfl, hm'.trans hm, (k.trans k').mono (by decide)⟩

theorem sub_one_allOnes : (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := rfl

/-- `recipGuess`: `d = m[w - 1]` into `x5`, for `m` at `x9` of `w` words, and
`guessV d` into `x10`, with `x4` all ones. -/
theorem recipGuess_ok {t : State} {B : Addr} {Z w eM : Nat} (hs : Scr t B Z)
    (h9 : t.gpr .x9 = off B eM) (h12 : t.gpr .x12 = BitVec.ofNat 64 w) (h7 : t.gpr .x7 = 0) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hM : eM + 8 * w ≤ Z) :
    WP isa (.block recipGuess) t fun t' => t'.gpr .x5 = word t.mem B (eM + 8 * (w - 1)) ∧
      t'.gpr .x10 = guessV (word t.mem B (eM + 8 * (w - 1))) ∧ t'.gpr .x4 = BitVec.allOnes 64 ∧ t'.mem = t.mem ∧
      Keep [.x2, .x3, .x4, .x5, .x10, .x13] t t' := by
  have hn := hs.nowrap
  rw [show recipGuess = ([.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x13 .x9 .x13, ld .x5 .x13,
      .subImm .x .x4 .x7 1, .logic .eor .x .x10 .x5 .x4] : List Instr) ++ (List.replicate 6 recipStep).flatten
      from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.x4, .x5, .x10, .x13] (Q := fun t' => t'.gpr .x5 = word t.mem B (eM + 8 * (w - 1)) ∧
      t'.gpr .x10 = word t.mem B (eM + 8 * (w - 1)) ^^^ BitVec.allOnes 64 ∧ t'.gpr .x4 = BitVec.allOnes 64 ∧
      t'.mem = t.mem)
    (by brun [h9, h12, h7, shl3_sub8 hw (show w < 2 ^ 61 by omega), off_add,
        hs.ld (show eM + 8 * (w - 1) + 8 ≤ Z by omega), sub_one_allOnes])
    (by decide) rfl (by decide +kernel)) fun t₁ ⟨⟨h5₁, h10₁, h4₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (recipSteps_ok 6 t₁ h4₁) fun t' ⟨h10', hm', k'⟩ => by
    rw [h5₁] at h10'
    exact
      ⟨(k'.gpr .x5 (by decide)).trans h5₁, by rw [h10', h10₁]; rfl,
        (k'.gpr .x4 (by decide)).trans h4₁, hm'.trans hm₁, (k₁.trans k').mono (by decide)⟩

/-! ## The corrections -/

theorem toNat_ofNat64 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem hi_lt {v D : Nat} (hv : v < 2 ^ 64) (hD : D < 2 ^ 64) : v * D / 2 ^ 64 < 2 ^ 64 := by
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  exact Nat.mul_lt_mul'' hv hD

theorem down_ok {t : State} {v D : Nat} (h10 : t.gpr .x10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (h5 : t.gpr .x5 = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) (h7 : t.gpr .x7 = 0) :
    WP isa (.block recipDown) t fun t' => (t'.gpr .x10 = BitVec.ofNat 64 (v - (over v D).toNat) ∧
      t'.gpr .x16 = BitVec.ofNat 64 (over v D).toNat ∧ t'.mem = t.mem) ∧ Keep [.x2, .x10, .x16] t t' := by
  refine WP.keep [.x2, .x10, .x16] ?_ (by decide) rfl (by decide +kernel)
  brun [recipDown, h10, h5, h7]
  rw [toNat_ofNat64 hv, toNat_ofNat64 hD, toNat_ofNat64 (hi_lt hv hD), zero_zero_add, Bool.toNat_false,
    Nat.add_zero]
  unfold over
  by_cases hc : 2 ^ 64 ≤ v * D / 2 ^ 64 + D
  · have hv1 := over_pos hD (show over v D = true from decide_eq_true hc)
    simp only [decide_eq_true hc, Bool.toNat_true]
    exact ⟨BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega), trivial⟩
  · simp only [decide_eq_false hc, Bool.toNat_false, Nat.sub_zero]
    exact ⟨BitVec.sub_zero _, trivial⟩

theorem up_ok {t : State} {v D : Nat} (h10 : t.gpr .x10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (h5 : t.gpr .x5 = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) (h7 : t.gpr .x7 = 0)
    (h15 : t.gpr .x15 = BitVec.ofNat 64 1) :
    WP isa (.block recipUp) t fun t' => (t'.gpr .x10 = BitVec.ofNat 64 (v + (up v D).toNat) ∧
      t'.gpr .x16 = BitVec.ofNat 64 (up v D).toNat ∧ t'.mem = t.mem) ∧ Keep [.x2, .x3, .x10, .x13, .x16] t t' := by
  refine WP.keep [.x2, .x3, .x10, .x13, .x16] ?_ (by decide) rfl (by decide +kernel)
  brun [recipUp, h10, h5, h7, h15]
  have e1 : (off (BitVec.ofNat 64 v) (1 + false.toNat)).toNat = (v + 1) % 2 ^ 64 := by
    simp only [off, Bool.toNat_false, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hlo := hi_lt (Nat.mod_lt (v + 1) (show 0 < 2 ^ 64 by decide)) hD
  rw [e1, toNat_ofNat64 hv, toNat_ofNat64 hD, toNat_ofNat64 hlo, zero_zero_add, zero_zero_add, or_bits,
    show (1#64).toNat = 1 from rfl, Bool.toNat_false, Nat.add_zero, Nat.add_zero]
  have hu : (!(decide (2 ^ 64 ≤ (v + 1) % 2 ^ 64 * D / 2 ^ 64 + D) || decide (2 ^ 64 ≤ v + 1))) = up v D := by
    unfold up over
    by_cases h : v + 1 = 2 ^ 64
    · simp only [h, decide_true, Bool.or_true, Bool.not_true, Bool.not_true, Bool.false_and, Nat.le_refl]
    · rw [Nat.mod_eq_of_lt (by omega), decide_eq_false (show ¬2 ^ 64 ≤ v + 1 by omega), decide_eq_false h,
        Bool.or_false, Bool.not_false, Bool.true_and]
  have hb : ∀ b : Bool, 1#64 - BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (!b).toNat := by decide
  rw [hb, hu]
  exact ⟨by rw [BitVec.ofNat_add], rfl⟩

/-! ## The loops -/

theorem bit_ne_zero (b : Bool) : (BitVec.ofNat 64 b.toNat != 0) = b := by cases b <;> rfl

/-- `recipDown` while it lowers `v`: then `(2^64 + v) d < 2^128`. -/
theorem downLoop_ok {t : State} {v D : Nat} (h10 : t.gpr .x10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (h5 : t.gpr .x5 = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) (h7 : t.gpr .x7 = 0) :
    WP isa (.loop (.block recipDown) (.nonzero .x .x16)) t fun t' => ∃ v', t'.gpr .x10 = BitVec.ofNat 64 v' ∧
      v' < 2 ^ 64 ∧ over v' D = false ∧ t'.mem = t.mem ∧ Keep [.x2, .x10, .x16] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => s.gpr .x10 = BitVec.ofNat 64 n ∧ n < 2 ^ 64 ∧ s.mem = t.mem ∧
    Keep [.x2, .x10, .x16] t s) (fun n s ⟨h1, h2, h3, k⟩ => ?_) v t ⟨h10, hv, rfl, Keep.refl _ _⟩
  refine WP.mono (down_ok h1 h2 ((k.gpr .x5 (by decide)).trans h5) hD ((k.gpr .x7 (by decide)).trans h7))
    fun s' ⟨⟨h1', h16, hm'⟩, k'⟩ => ?_
  have hc : isa.eval (.nonzero .x .x16) s' = some (over n D) := by rw [eval_nonzero, h16, bit_ne_zero]
  cases ho : over n D
  · rw [ho, Bool.toNat_false, Nat.sub_zero] at h1'
    exact .inl ⟨by rw [hc, ho], n, h1', h2, ho, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · have hn := over_pos hD ho
    rw [ho, Bool.toNat_true] at h1'
    exact .inr ⟨by rw [hc, ho], n - 1, by omega_using [hn], h1', by omega_using [h2], hm'.trans h3,
      (k.trans k').mono (by decide)⟩

/-- `recipUp` while it raises `v`, from `v` with `(2^64 + v) d < 2^128`: then
also `up v d` is false. -/
theorem upLoop_ok {t : State} {v D : Nat} (h10 : t.gpr .x10 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (ho : over v D = false) (h5 : t.gpr .x5 = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) (h7 : t.gpr .x7 = 0)
    (h15 : t.gpr .x15 = BitVec.ofNat 64 1) :
    WP isa (.loop (.block recipUp) (.nonzero .x .x16)) t fun t' => ∃ v', t'.gpr .x10 = BitVec.ofNat 64 v' ∧
      v' < 2 ^ 64 ∧ over v' D = false ∧ up v' D = false ∧ t'.mem = t.mem ∧
      Keep [.x2, .x3, .x10, .x13, .x16] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ u, n = 2 ^ 64 - u ∧ s.gpr .x10 = BitVec.ofNat 64 u ∧
    u < 2 ^ 64 ∧ over u D = false ∧ s.mem = t.mem ∧ Keep [.x2, .x3, .x10, .x13, .x16] t s)
    (fun n s ⟨u, hn, h1, h2, ho', h3, k⟩ => ?_) (2 ^ 64 - v) t ⟨v, rfl, h10, hv, ho, rfl, Keep.refl _ _⟩
  refine WP.mono (up_ok h1 h2 ((k.gpr .x5 (by decide)).trans h5) hD ((k.gpr .x7 (by decide)).trans h7)
    ((k.gpr .x15 (by decide)).trans h15)) fun s' ⟨⟨h1', h16, hm'⟩, k'⟩ => ?_
  have hc : isa.eval (.nonzero .x .x16) s' = some (up u D) := by rw [eval_nonzero, h16, bit_ne_zero]
  cases hu : up u D
  · rw [hu, Bool.toNat_false, Nat.add_zero] at h1'
    exact .inl ⟨by rw [hc, hu], u, h1', h2, ho', hu, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · rw [hu, Bool.toNat_true] at h1'
    unfold up at hu
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
    exact .inr ⟨by rw [hc]; unfold up; rw [hu.2, decide_eq_false hu.1]; rfl,
      2 ^ 64 - (u + 1), by omega_using [hn, h2, hu.1], u + 1, rfl, h1', by omega_using [h2, hu.1], hu.2,
      hm'.trans h3, (k.trans k').mono (by decide)⟩

/-! ## The reciprocal -/

/-- `recipN`: `v = ⌊(2^128 - 1) / d⌋ - 2^64` for `d = m[w - 1] ≥ 2^63` into
the word at `x6`, for `m` at `x9` of `w` words, as `recip` (`r2dRecip_ok`). -/
theorem r2dRecipN_ok {s : State} {B : Addr} {Z w eM eV : Nat} (hs : Scr s B Z)
    (h9 : s.gpr .x9 = off B eM) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h6 : s.gpr .x6 = off B eV)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : eM + 8 * w ≤ Z) (hV : eV + 8 ≤ Z)
    (hd : 2 ^ 63 ≤ (word s.mem B (eM + 8 * (w - 1))).toNat) :
    WP isa recipN s fun t =>
      (word t.mem B eV).toNat = (2 ^ 128 - 1) / (word s.mem B (eM + 8 * (w - 1))).toNat - 2 ^ 64 ∧
      Outside B eV 8 s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x5, .x10, .x13, .x15, .x16] s t := by
  have hn := hs.nowrap
  generalize hD : word s.mem B (eM + 8 * (w - 1)) = Dw at hd
  have hD' := Dw.isLt
  have eD : Dw = BitVec.ofNat 64 Dw.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold recipN
  simp only [seqs]
  refine WP.seq (WP.mono (recipGuess_ok hs h9 h12 h7 hw hw' hM) fun t₁ ⟨h5₁, _, _, hm₁, k₁⟩ => ?_)
  rw [hD, eD] at h5₁
  have h7₁ : t₁.gpr .x7 = 0 := (k₁.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (downLoop_ok (v := (t₁.gpr .x10).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (t₁.gpr .x10).isLt h5₁ hD' h7₁) fun t₂ ⟨v₂, h10₂, hv₂, ho₂, hm₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = BitVec.ofNat 64 1 ∧ t.mem = t₂.mem)
    (by brun) (by decide)) fun t₃ ⟨⟨h15₃, hm₃⟩, k₃⟩ => ?_)
  have k23 := k₂.trans k₃
  refine WP.seq (WP.mono (upLoop_ok ((k₃.gpr .x10 (by decide)).trans h10₂) hv₂ ho₂
    ((k23.gpr .x5 (by decide)).trans h5₁) hD' ((k23.gpr .x7 (by decide)).trans h7₁) h15₃)
    fun t₄ ⟨v₄, h10₄, hv₄, ho₄, hu₄, hm₄, k₄⟩ => ?_)
  have k14 := (k₁.trans k23).trans k₄
  have hs₄ := hs.congr k14.wr
  have h6₄ : t₄.gpr .x6 = off B eV := (k14.gpr .x6 (by decide)).trans h6
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₄.mem.writeW (off B eV) (t₄.gpr .x10))
    (by brun [h6₄, hs₄.st hV]) (by decide)) fun t' ⟨hm', k'⟩ => ?_
  have hvx := recip_exact hd hD' ho₄ hu₄
  have hm : t₄.mem = s.mem := by rw [hm₄, hm₃, hm₂, hm₁]
  refine ⟨?_, ?_, (k14.trans k').mono (by decide)⟩
  · rw [hm', word_writeW_self, h10₄, toNat_ofNat64 hv₄, hvx]
  · rw [hm', hm]
    exact writeW_outside _ _ _ (by omega)

end VG.Proof.Bignum.AArch64
