import VerifiedGarbage.Proof.Bignum.AArch64.Rounds

/-!
# Multiword arithmetic on AArch64: the conditional subtraction

`subMod` computes `D = T - m` over `w` words, the borrow `c` kept in the
carry flag (clear on a borrow) from word to word, then subtracts it from
the top word of `T`: the carry flag ends clear iff `T_w < c`, which is
`T < m` for `T < 2 · 2^(64 w)` (`subMod_ok`). `selectAcc` then writes `T`
if the flag is clear and `D` if it is set (`selectAcc_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A subtraction with borrow (`sbcs`): the difference, the subtrahend and
the borrow in (`!C`) are the minuend and the borrow out. -/
theorem sbcs_toNat (a b : BitVec 64) (C : Bool) :
    (a + ~~~b + BitVec.ofNat 64 C.toNat).toNat + b.toNat + (!C).toNat =
      a.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + C.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hnb : (~~~b).toNat = 2 ^ 64 - 1 - b.toNat := by rw [BitVec.toNat_not]
  have hnc : (!C).toNat = 1 - C.toNat := by cases C <;> rfl
  have hc1 := Bool.toNat_le C
  rw [hnb, hnc]
  generalize C.toNat = c at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hnb]
  by_cases h : 2 ^ 64 ≤ a.toNat + (2 ^ 64 - 1 - b.toNat) + c <;>
  simp only [h, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.toNat_true,
    Bool.toNat_false] <;> omega

/-- The borrow out of the top word: `!C` subtracted from `X`. -/
theorem top_borrow (X : BitVec 64) (C : Bool) :
    decide (2 ^ 64 ≤ X.toNat + (~~~(0 : BitVec 64)).toNat + C.toNat) = !decide (X.toNat < (!C).toNat) := by
  rw [show (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 from rfl]
  cases C <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false] <;>
  by_cases h : X.toNat < 1 <;> simp [h] <;> omega

/-! ## `T - m` -/

/-- After `j` words of `subMod`'s loop from `s₀`: `D_j + m_j = T_j + 2^(64 j) c`
for the low `j` words `D_j` of the difference, `m_j` of `m`, `T_j` of `T`,
and the borrow `c`, the complement of the carry flag. -/
structure SubInv (s₀ : State) (B : Addr) (Z eA eN eT : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eN + 8 * j)
  x13 : t.gpr .x13 = off B (eT + 8 * j)
  out : Outside B eT (8 * j) s₀.mem t.mem
  val : wv t.mem B eT j + wv s₀.mem B eN j = wv s₀.mem B eA j + 2 ^ (64 * j) * (!t.c).toNat

theorem subStep_ok {s₀ : State} {B : Addr} {Z w eA eN eT : Nat}
    (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * w ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT) {j : Nat} (hj : j < w)
    {t : State} (hI : SubInv s₀ B Z eA eN eT j t) :
    WP isa (.block ([ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16, next .x17,
        next .x13] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      SubInv s₀ B Z eA eN eT (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x13, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eT + 8 * j)) (word t.mem B (eA + 8 * j) + ~~~word t.mem B (eN + 8 * j) +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * j)).toNat + (~~~word t.mem B (eN + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eN + 8 * j + 8) ∧
      t₁.gpr .x13 = off B (eT + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.x13, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eT + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17, h13⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x13 (by decide), h13, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := sbcs_toNat (word t.mem B (eA + 8 * j)) (word t.mem B (eN + 8 * j)) t.c
    rw [hx, hy] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ]
    rw [hx, hy]
    grind

/-- `subMod`: `D = T - m` over `w` words into the array at `x6` (`eT`), its
borrow `c`, and the carry flag clear iff `T_w < c` for the word `w` of `T`
(that is, iff `T < m` when `T < 2 · 2^(64 w)`). -/
theorem subMod_ok {s : State} {B : Addr} {Z w eA eN eT : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN) (h6 : s.gpr .x6 = off B eT)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 1) ≤ Z) (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT) :
    WP isa subMod s fun t => ∃ c : Bool,
      t.c = !decide ((word s.mem B (eA + 8 * w)).toNat < c.toNat) ∧
      wv t.mem B eT w + wv s.mem B eN w = wv s.mem B eA w + 2 ^ (64 * w) * c.toNat ∧
      Outside B eT (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold subMod
  refine WP.seq (WP.mono (WP.keep [.x3, .x13, .x14, .x16, .x17] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x17 = off B eN ∧ t.gpr .x13 = off B eT ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧
    t.mem = s.mem) (by brun [h8, h10, h6, h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h13, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SubInv s₁ B Z eA eN eT 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl,
      Outside.refl _ _ _ _, by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (SubInv s₁ B Z eA eN eT)
    (fun j hj t hI _ => subStep_ok (by omega) hN hT (by omega) sN hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7)
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (by omega) (by omega), hm₁]
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t.mem ∧
      t'.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * w)).toNat + (~~~(0 : BitVec 64)).toNat + t.c.toNat))
    (by brun [hI.x16, t7, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', hc'⟩, k'⟩ => ?_
  refine ⟨!t.c, ?_, ?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hc', top_borrow, hX]
  · rw [hm', ← hm₁]; exact hI.val
  · rw [hm', ← hm₁]; exact hI.out

/-! ## The selection -/

structure SelInv (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x6, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x6 : t.gpr .x6 = off B (eT + 8 * j)
  x5 : t.gpr .x5 = off B (eo + 8 * j)
  c : t.c = !lt
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

theorem selectAcc_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h6 : s.gpr .x6 = off B eT) (h5 : s.gpr .x5 = off B eo)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) {lt : Bool} (hc : s.c = !lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = s.c ∧ t.mem = s.mem) (by brun [h8, h12])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SelInv s₁ B Z eA eT eo lt 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [k₁.gpr .x6 (by decide), h6]; rfl,
      by rw [k₁.gpr .x5 (by decide), h5]; rfl, hc₁.trans hc, Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (SelInv s₁ B Z eA eT eo lt) ?_ h0 h14)
    fun t hI => ⟨by rw [hI.val, hm₁], by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  intro j hj t hI _
  have hx : word t.mem B (eA + 8 * j) = word s₁.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eT + 8 * j) = word s₁.mem B (eT + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if t.c then word t.mem B (eT + 8 * j) else word t.mem B (eA + 8 * j)) ∧ t₁.c = t.c ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x6 = off B (eT + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8)) (by
      brun [hI.x16, hI.x6, hI.x5, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
        hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16', h6', h5'⟩, k₁'⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ =>
    ⟨?_, by rw [h14', k₁'.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁'.wr), (hI.keep.trans (k₁'.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x6 (by decide), h6', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5', Nat.mul_succ, Nat.add_assoc], by rw [hc'', hc', hI.c], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val, hI.c, hx, hy]
    cases lt <;> simp [wv]

end VG.Proof.Bignum.AArch64
