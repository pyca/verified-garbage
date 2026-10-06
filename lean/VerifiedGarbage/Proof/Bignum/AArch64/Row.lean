import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-!
# Multiword arithmetic on AArch64: `acc += a_i B`

`mulAddRow` adds `x1 · B` (the `w` words at `x9`) into the accumulator (the
`w + 2` words at `x8`): a loop of multiply-accumulate steps over the `w`
words of `B`, then the last carry into words `w` and `w + 1`
(`mulAddRow_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `cnt -= 1`. -/
theorem dec_ok (s : State) (cnt : Reg)
    (hc : writesOnly [cnt] (.block [.subImm .x cnt cnt 1]) = true := by decide)
    (hv : Code.allInstrs keepsV (.block [.subImm .x cnt cnt 1] : Prog isa) = true := by decide +kernel) :
    WP isa (.block [.subImm .x cnt cnt 1]) s fun t =>
      (t.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [cnt] s t := by
  refine WP.keep (c := .block [.subImm .x cnt cnt 1]) [cnt] ?_ hc rfl hv
  brun

/-! ## The loop of `mulAddRow` -/

/-- After `j` steps of `mulAddRow`'s loop from the state `s₀`: the
accumulator's low `j` words and the carry `x2` hold its low `j` words plus
`x1` times those of `B`. -/
structure RowInv (s₀ : State) (B : Addr) (Z eA eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eb + 8 * j)
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * (t.gpr .x2).toNat =
    wv s₀.mem B eA j + (s₀.gpr .x1).toNat * wv s₀.mem B eb j

theorem rowStep_ok {s₀ : State} {B : Addr} {Z w eA eb : Nat} (h7 : s₀.gpr .x7 = 0)
    (hA : eA + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eb ∨ eb + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State}
    (hI : RowInv s₀ B Z eA eb j t) :
    WP isa (.block (mac false ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      RowInv s₀ B Z eA eb (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t1 : t.gpr .x1 = s₀.gpr .x1 := hI.keep.gpr .x1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x2, .x3, .x4, .x16, .x17] (mac_ok t false hI.scr hI.x16 hI.x17 t7
    (by omega) (by simp only [Bool.false_eq_true, ite_false]; omega) (by omega))
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨lo, hm, hv, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hv
  have hmem : t'.mem = t.mem.writeW (off B (eA + 8 * j)) lo := hm'.trans hm
  -- The words read: `x` of the accumulator and `y` of `B`, both as on entry.
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : word t.mem B (eb + 8 * j) = word s₀.mem B (eb + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), k'.gpr .x2 (by decide)]
    simp only [wv]
    rw [hx, hy, t1] at hv
    have hval := hI.val
    rw [pow64_succ]
    grind

/-! ## The top words -/

/-- Words `w` and `w + 1` (at `x16`) plus the carry `x2`. -/
theorem rowTop_ok {t : State} {B : Addr} {Z d : Nat} (hs : Scr t B Z)
    (h16 : t.gpr .x16 = off B d) (h7 : t.gpr .x7 = 0) (hA : d + 16 ≤ Z) :
    WP isa (.block rowTop) t fun t' =>
      t'.mem = (t.mem.writeW (off B d) (word t.mem B d + t.gpr .x2)).writeW (off B (d + 8))
        (word t.mem B (d + 8) + BitVec.ofNat 64
          (decide (2 ^ 64 ≤ (word t.mem B d).toNat + (t.gpr .x2).toNat)).toNat) ∧
      Keep [.x3] t t' := by
  have hn := hs.nowrap
  have hX : (t.mem.writeW (off B d) (t.mem.readW (off B d) 64 + t.gpr .x2)).readW (off B (d + 8)) 64 =
      t.mem.readW (off B (d + 8)) 64 :=
    (writeW_outside t.mem B _ (by omega)).word (Or.inr (Nat.le_refl _)) (by omega)
  refine WP.keep [.x3] ?_ (by decide) (by decide) (by decide +kernel)
  unfold rowTop
  brun [h16, h7, hs.ld (show d + 8 ≤ Z by omega), hs.st (show d + 8 ≤ Z by omega),
    hs.ld (show d + 8 + 8 ≤ Z by omega), hs.st (show d + 8 + 8 ≤ Z by omega)]
  simp only [Bool.toNat_false, Nat.add_zero, add_ofNat0, add_zero64]
  simp only [hX]

/-- Two words plus a carry and its carry, as numbers, if they fit. -/
theorem addc2_toNat (X Y c : BitVec 64) (hfit : X.toNat + c.toNat + 2 ^ 64 * Y.toNat < 2 ^ 128) :
    (X + c).toNat + 2 ^ 64 * (Y + BitVec.ofNat 64 (decide (2 ^ 64 ≤ X.toNat + c.toNat)).toNat).toNat =
      X.toNat + c.toNat + 2 ^ 64 * Y.toNat := by
  have hX := X.isLt; have hY := Y.isLt; have hc := c.isLt
  by_cases h : 2 ^ 64 ≤ X.toNat + c.toNat <;>
  simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, BitVec.toNat_add,
    BitVec.toNat_ofNat] <;> omega

/-- The value after `rowTop`: `X + c` and `Y` plus its carry, if they fit. -/
theorem rowTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    wv ((m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)).writeW
        (off B (eA + 8 * w + 8)) (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
          (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat))
        B eA (w + 2) =
      wv m B eA w + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat) := by
  have o1 := writeW_outside m B (word m B (eA + 8 * w) + c) (d := eA + 8 * w) (by omega)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)) B
    (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat)
    (d := eA + 8 * w + 8) (by omega)
  have hc := addc2_toNat (word m B (eA + 8 * w)) (word m B (eA + 8 * w + 8)) c hfit
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega,
    word_writeW_self, o2.word (Or.inl (Nat.le_refl _)) (by omega), word_writeW_self,
    o2.wv (Or.inl (by omega)) (by omega), o1.wv (Or.inl (Nat.le_refl _)) (by omega), pow64_succ, ← hc]
  grind

/-! ## `mulAddRow` -/

/-- `acc += x1 · B` (`mulAddRow`), if the sum fits in `w + 2` words. -/
theorem mulAddRow_ok {s : State} {B : Addr} {Z w eA eb : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eb) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA)
    (hbound : wv s.mem B eA (w + 2) + (s.gpr .x1).toNat * wv s.mem B eb w < 2 ^ (64 * (w + 2))) :
    WP isa mulAddRow s fun t =>
      wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) + (s.gpr .x1).toNat * wv s.mem B eb w ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold mulAddRow
  refine WP.seq (WP.mono (WP.keep [.x2, .x14, .x16, .x17] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x17 = off B eb ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧ t.mem = s.mem)
    (by brun [h8, h9, h12]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, h2, hm₁⟩, k₁⟩ => ?_)
  have s₁7 : s₁.gpr .x7 = 0 := (k₁.gpr .x7 (by decide)).trans h7
  have s₁1 : s₁.gpr .x1 = s.gpr .x1 := k₁.gpr .x1 (by decide)
  have h0 : RowInv s₁ B Z eA eb 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _,
      by rw [h2]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (RowInv s₁ B Z eA eb)
    (fun j hj t hI _ => rowStep_ok s₁7 (by omega) hb (by omega) hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans s₁7
  refine WP.mono (rowTop_ok hI.scr hI.x16 t7 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  -- The words above the loop's, as on entry.
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁, s₁1] at hval
  have e2 := wv_top2 s.mem B eA w
  -- The sum fits: `X + c + 2⁶⁴ Y < 2¹²⁸`.
  have hfit : (word t.mem B (eA + 8 * w)).toNat + (t.gpr .x2).toNat +
      2 ^ 64 * (word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((word s.mem B (eA + 8 * w)).toNat + (t.gpr .x2).toNat +
        2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega]
      have := wv_lt t.mem B eA w
      grind
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', rowTop_val t.mem B hn (show eA + 8 * w + 16 ≤ Z by omega) _ hfit, hX, hY, e2]
    grind
  · rw [hm']
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega)]
    exact (hI.out x (by omega)).trans (by rw [hm₁])

end VG.Proof.Bignum.AArch64
