import VerifiedGarbage.Proof.Bignum.AArch64.Row

/-!
# Multiword arithmetic on AArch64: `acc := (acc + u m) / 2⁶⁴`

`reduceRow` adds `u m` to the accumulator `T` (`w + 2` words at `x8`),
`u = T₀ (-m⁻¹) mod 2⁶⁴` (`-m⁻¹` in `x15`, `m` the `w` words at `x10`), so
that the low word is zero, and stores the sum shifted down one word:
`2⁶⁴ T' = T + u m` (`reduceRow_ok`).

* `redHead` computes `u` into `x1` and the carry of `T₀ + u m₀`.
* The loop, for `j = 1, …, w - 1`, is a multiply-accumulate step storing
  word `j - 1` (`RedInv`).
* `redTop` adds the carry into words `w` and `w + 1`, stored one down.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem ofNat_sub_one {w : Nat} (hw : 1 ≤ w) : BitVec.ofNat 64 w - 1#64 = BitVec.ofNat 64 (w - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- The carry of `T₀ + u m₀` when its low word is zero: `2⁶⁴` times the high
word of `u m₀` plus the carry is the sum. -/
theorem redc_carry (u n t : BitVec 64) (hlow : (u.toNat * n.toNat + t.toNat) % 2 ^ 64 = 0) :
    2 ^ 64 * (BitVec.ofNat 64 (u.toNat * n.toNat / 2 ^ 64) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (u * n).toNat + t.toNat)).toNat).toNat =
      u.toNat * n.toNat + t.toNat := by
  have hu := u.isLt; have hn := n.isLt; have ht := t.isLt
  have hle : u.toNat * n.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  by_cases h : 2 ^ 64 ≤ (u * n).toNat + t.toNat <;>
  simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at h ⊢ <;>
  generalize u.toNat * n.toNat = P at * <;>
  omega_arith

theorem redHead_ok {s : State} {B : Addr} {Z w eA eN : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hA : eA + 8 ≤ Z) (hN : eN + 8 ≤ Z)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block redHead) s fun t =>
      (t.mem = s.mem ∧
      (t.gpr .x1).toNat = (word s.mem B eA).toNat * (s.gpr .x15).toNat % 2 ^ 64 ∧
      2 ^ 64 * (t.gpr .x2).toNat = (t.gpr .x1).toNat * (word s.mem B eN).toNat + (word s.mem B eA).toNat ∧
      t.gpr .x16 = off B eA ∧ t.gpr .x17 = off B (eN + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1)) ∧
      Keep [.x1, .x2, .x3, .x4, .x14, .x16, .x17] s t := by
  refine WP.keep [.x1, .x2, .x3, .x4, .x14, .x16, .x17] ?_ (by decide) (by decide) (by decide +kernel)
  unfold redHead
  brun [h8, h10, h12, h7, hs.ld hA, hs.ld hN]
  simp only [Bool.toNat_false, Nat.add_zero, add_zero64]
  refine ⟨BitVec.toNat_mul _ _, ?_, ofNat_sub_one hw⟩
  have hlow := mont_low (word s.mem B eA).toNat (s.gpr .x15).toNat (word s.mem B eN).toNat hinv
  rw [← BitVec.toNat_mul] at hlow
  exact redc_carry _ _ _ hlow

/-! ## The loop -/

/-- After the steps up to `j - 1` of `reduceRow`'s loop from the state `s₁`
(after `redHead`): words `0, …, j - 2` hold the low words of
`(T + u m) / 2⁶⁴` so far, and `x2` the carry. -/
structure RedInv (s₁ : State) (B : Addr) (Z eA eN : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4, .x14, .x16, .x17] s₁ t
  x16 : t.gpr .x16 = off B (eA + 8 * (j - 1))
  x17 : t.gpr .x17 = off B (eN + 8 * j)
  out : Outside B eA (8 * (j - 1)) s₁.mem t.mem
  val : 2 ^ 64 * (wv t.mem B eA (j - 1) + 2 ^ (64 * (j - 1)) * (t.gpr .x2).toNat) =
    wv s₁.mem B eA j + (s₁.gpr .x1).toNat * wv s₁.mem B eN j

theorem redStep_ok {s₁ : State} {B : Addr} {Z w eA eN : Nat} (h7 : s₁.gpr .x7 = 0)
    (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eN ∨ eN + 8 * w ≤ eA) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State}
    (hI : RedInv s₁ B Z eA eN j t) :
    WP isa (.block (mac true ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      RedInv s₁ B Z eA eN (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t1 : t.gpr .x1 = s₁.gpr .x1 := hI.keep.gpr .x1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x2, .x3, .x4, .x16, .x17] (mac_ok t true hI.scr hI.x16 hI.x17 t7
    (by omega_arith) (by simp only [ite_true]; omega_arith) (by omega_arith))
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨lo, hm, hv, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  simp only [ite_true] at hv
  have hmem : t'.mem = t.mem.writeW (off B (eA + 8 * (j - 1))) lo := hm'.trans hm
  have e8 : eA + 8 * (j - 1) + 8 = eA + 8 * j := by omega_arith
  rw [e8] at hv
  have hx : word t.mem B (eA + 8 * j) = word s₁.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (by omega_arith)) (by omega_arith)
  have hy : word t.mem B (eN + 8 * j) = word s₁.mem B (eN + 8 * j) :=
    hI.out.word (by omega_arith) (by omega_arith)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, e8, show j + 1 - 1 = j by omega_arith],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hmem, show j + 1 - 1 = j - 1 + 1 by omega_arith, wv_writeW_top _ _ _ _ _ (by omega_arith), k'.gpr .x2 (by decide)]
    simp only [wv]
    rw [hx, hy, t1] at hv
    have hval := hI.val
    have hp : 2 ^ 64 * 2 ^ (64 * (j - 1)) = 2 ^ (64 * j) := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    rw [show 64 * (j - 1 + 1) = 64 * j by omega_arith]
    grind

/-! ## The top words -/

/-- The memory `redTop` leaves: `X + c` at word `w - 1`, `Y` plus the carry
at word `w`, 0 at word `w + 1`, for the words `X`, `Y` at `w`, `w + 1`. -/
def redTopMem (m : Mem) (B : Addr) (eA w : Nat) (c : BitVec 64) : Mem :=
  ((m.writeW (off B (eA + 8 * (w - 1))) (word m B (eA + 8 * w) + c)).writeW (off B (eA + 8 * w))
    (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat)).writeW
    (off B (eA + 8 * w + 8)) (0 : BitVec 64)

theorem redTop_ok {t : State} {B : Addr} {Z w eA : Nat} (hs : Scr t B Z) (hw : 1 ≤ w)
    (h16 : t.gpr .x16 = off B (eA + 8 * (w - 1))) (h7 : t.gpr .x7 = 0) (hA : eA + 8 * w + 16 ≤ Z) :
    WP isa (.block redTop) t fun t' => t'.mem = redTopMem t.mem B eA w (t.gpr .x2) ∧ Keep [.x3] t t' := by
  have hn := hs.nowrap
  have e1 : eA + 8 * (w - 1) + 8 = eA + 8 * w := by omega_arith
  have e2 : eA + 8 * (w - 1) + 16 = eA + 8 * w + 8 := by omega_arith
  have hY : (t.mem.writeW (off B (eA + 8 * (w - 1))) (t.mem.readW (off B (eA + 8 * w)) 64 + t.gpr .x2)).readW
      (off B (eA + 8 * w + 8)) 64 = t.mem.readW (off B (eA + 8 * w + 8)) 64 :=
    (writeW_outside t.mem B _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith)
  refine WP.keep [.x3] ?_ (by decide) (by decide) (by decide +kernel)
  unfold redTop redTopMem
  brun [h16, h7, e1, e2, hs.ld (show eA + 8 * w + 8 ≤ Z by omega_arith),
    hs.st (show eA + 8 * (w - 1) + 8 ≤ Z by omega_arith), hs.st (show eA + 8 * w + 8 ≤ Z by omega_arith),
    hs.ld (show eA + 8 * w + 8 + 8 ≤ Z by omega_arith), hs.st (show eA + 8 * w + 8 + 8 ≤ Z by omega_arith)]
  simp only [Bool.toNat_false, Nat.add_zero, add_zero64, BitVec.add_zero]
  simp only [hY]

/-- The value after `redTop`, times `2⁶⁴`, if the top fits. -/
theorem redTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64) (hw : 1 ≤ w)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    2 ^ 64 * wv (redTopMem m B eA w c) B eA (w + 2) =
      2 ^ 64 * wv m B eA (w - 1) + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat) := by
  unfold redTopMem
  generalize hX : word m B (eA + 8 * w) = X at hfit
  generalize hY : word m B (eA + 8 * w + 8) = Y at hfit
  have o1 := writeW_outside m B (X + c) (d := eA + 8 * (w - 1)) (by omega_arith)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * (w - 1))) (X + c)) B
    (Y + BitVec.ofNat 64 (decide (2 ^ 64 ≤ X.toNat + c.toNat)).toNat) (d := eA + 8 * w) (by omega_arith)
  have o3 := writeW_outside ((m.writeW (off B (eA + 8 * (w - 1))) (X + c)).writeW (off B (eA + 8 * w))
    (Y + BitVec.ofNat 64 (decide (2 ^ 64 ≤ X.toNat + c.toNat)).toNat)) B (0 : BitVec 64)
    (d := eA + 8 * w + 8) (by omega_arith)
  have hc := addc2_toNat X Y c hfit
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega_arith
  rw [show w + 2 = w - 1 + 1 + 1 + 1 by omega_arith, wv, wv, wv, show eA + 8 * (w - 1 + 1 + 1) = eA + 8 * w + 8 by omega_arith,
    show eA + 8 * (w - 1 + 1) = eA + 8 * w by omega_arith, word_writeW_self,
    o3.word (Or.inl (Nat.le_refl _)) (by omega_arith), word_writeW_self,
    o3.word (Or.inl (by omega_arith)) (by omega_arith), o2.word (Or.inl (by omega_arith)) (by omega_arith), word_writeW_self,
    o3.wv (Or.inl (by omega_arith)) (by omega_arith), o2.wv (Or.inl (by omega_arith)) (by omega_arith),
    o1.wv (Or.inl (Nat.le_refl _)) (by omega_arith), show 64 * (w - 1 + 1 + 1) = 64 * w + 64 by omega_arith,
    show 64 * (w - 1 + 1) = 64 * w by omega_arith, Nat.pow_add]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, ← hc]
  grind

/-! ## The row -/

/-- `2⁶⁴ T' = T + u m` (`reduceRow`), for `u = T₀ (-m⁻¹) mod 2⁶⁴`, if `T + u m`
fits in `w + 2` words. -/
theorem reduceRow_ok {s : State} {B : Addr} {Z w eA eN : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0)
    (hbound : ∀ u < 2 ^ 64, wv s.mem B eA (w + 2) + u * wv s.mem B eN w < 2 ^ (64 * (w + 2))) :
    WP isa reduceRow s fun t =>
      2 ^ 64 * wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) +
        (word s.mem B eA).toNat * (s.gpr .x15).toNat % 2 ^ 64 * wv s.mem B eN w ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold reduceRow
  refine WP.seq (WP.mono (redHead_ok hs h8 h10 h12 h7 (by omega_arith) (by omega_arith) (by omega_arith) hinv)
    fun s₁ ⟨⟨hm₁, hu, hc₁, h16, h17, h14⟩, k₁⟩ => ?_)
  have s₁7 : s₁.gpr .x7 = 0 := (k₁.gpr .x7 (by decide)).trans h7
  have h0 : RedInv s₁ B Z eA eN 1 s₁ := by
    refine ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17], Outside.refl _ _ _ _, ?_⟩
    simp only [wv, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
    rw [hc₁, hm₁]
    omega_arith
  refine WP.seq (WP.mono (wp_countdown (N := w - 1) (by omega_arith) (by omega_arith)
    (fun i => RedInv s₁ B Z eA eN (i + 1))
    (fun i hi t hI _ => redStep_ok s₁7 (by omega_arith) hN (by omega_arith) (by omega_arith) (by omega_arith) hI) h0 h14)
    fun t hI => ?_)
  rw [show w - 1 + 1 = w by omega_arith] at hI
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans s₁7
  refine WP.mono (redTop_ok hI.scr (by omega_arith) hI.x16 t7 (by omega_arith)) fun t' ⟨hm', k'⟩ => ?_
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (by omega_arith)) (by omega_arith), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega_arith)) (by omega_arith), hm₁]
  have hval := hI.val
  rw [hm₁] at hval
  have hb := hbound _ (s₁.gpr .x1).isLt
  have e2 := wv_top2 s.mem B eA w
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega_arith
  -- The top fits.
  have hfit : (word t.mem B (eA + 8 * w)).toNat + (t.gpr .x2).toNat +
      2 ^ 64 * (word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((word s.mem B (eA + 8 * w)).toNat + (t.gpr .x2).toNat +
        2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega_arith, Nat.mul_add, Nat.mul_add]
      rw [Nat.mul_add, ← Nat.mul_assoc (2 ^ 64), hp] at hval
      rw [Nat.mul_add] at e2
      omega_using [hval, hb, e2]
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', redTop_val t.mem B hn (by omega_arith) (show eA + 8 * w + 16 ≤ Z by omega_arith) _ hfit, hX, hY, e2, ← hu]
    grind
  · rw [hm']
    intro x hx
    unfold redTopMem
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith), writeW_outside _ B _ (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by omega_arith)]
    exact (hI.out x (by omega_arith)).trans (by rw [hm₁])

end VG.Proof.Bignum.AArch64
