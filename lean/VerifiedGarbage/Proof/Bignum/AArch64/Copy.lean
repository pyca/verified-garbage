import VerifiedGarbage.Proof.Bignum.AArch64.R2

/-!
# Multiword arithmetic on AArch64: copies and comparisons

`copyWords` copies `w` words between two places that do not overlap
(`copyWords_ok`); `cmpLoop` computes the borrow of `X - N` over `w` words in
the carry flag, which ends clear iff `X < N` (`cmpLoop_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

structure CopyInv (s₀ : State) (S D : Addr) (eS eD : Nat) (j : Nat) (t : State) : Prop where
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off S (eS + 8 * j)
  x17 : t.gpr .x17 = off D (eD + 8 * j)
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i)
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem copyStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat} (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : CopyInv s₀ S D eS eD j t) :
    WP isa (.block ([ld .x3 .x16, st .x3 .x17, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => CopyInv s₀ S D eS eD (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.wr]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j)) ∧
      t₁.gpr .x16 = off S (eS + 8 * j + 8) ∧ t₁.gpr .x17 = off D (eD + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hld, hst]; exact congrArg _ hv) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `copyWords`: the `w` words at `S + eS` (`x16`) to `D + eD` (`x17`), which
they do not overlap, changing only those. -/
theorem copyWords_ok {s : State} {S D : Addr} {eS eD w : Nat}
    (h16 : s.gpr .x16 = off S eS) (h17 : s.gpr .x17 = off D eD) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa copyWords s fun t =>
      wv t.mem D eD w = wv s.mem S eS w ∧ (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i)) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ t.gpr .x16 = off S (eS + 8 * w) ∧
      t.gpr .x17 = off D (eD + 8 * w) ∧ Keep [.x3, .x14, .x16, .x17] s t := by
  unfold copyWords
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h14, hm₁⟩, k₁⟩ => ?_)
  have h0 : CopyInv s S D eS eD 0 s₁ :=
    ⟨k₁.mono (by decide), by rw [k₁.gpr .x16 (by decide), h16]; rfl, by rw [k₁.gpr .x17 (by decide), h17]; rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _), by rw [hm₁]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (CopyInv s S D eS eD)
    (fun j hj t hI _ => copyStep_ok hD hrd hwr hsep hj hI) h0 h14) fun t hI => ?_
  exact ⟨wv_congr2 hI.done, hI.done, hI.frame, hI.x16, hI.x17, hI.keep⟩

/-! ## Comparisons -/

structure CmpInv (s₀ : State) (B : Addr) (Z eX eN : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  mem : t.mem = s₀.mem
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eN + 8 * j)
  val : ∃ d : Nat, d < 2 ^ (64 * j) ∧
    d + wv s₀.mem B eN j = wv s₀.mem B eX j + 2 ^ (64 * j) * (!t.c).toNat

theorem cmpStep_ok {s₀ : State} {B : Addr} {Z w eX eN : Nat} (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : CmpInv s₀ B Z eX eN j t) :
    WP isa (.block ([ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => CmpInv s₀ B Z eX eN (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  obtain ⟨d, hd, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j)).toNat + (~~~word t.mem B (eN + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x3 = word t.mem B (eX + 8 * j) + ~~~word t.mem B (eN + 8 * j) + BitVec.ofNat 64 t.c.toNat ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eN + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, hc, h3, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hs := sbcs_toNat (word t.mem B (eX + 8 * j)) (word t.mem B (eN + 8 * j)) t.c
  rw [hI.mem] at hs
  generalize (word s₀.mem B (eX + 8 * j) + ~~~word s₀.mem B (eN + 8 * j) + BitVec.ofNat 64 t.c.toNat) = r at hs
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ⟨d + 2 ^ (64 * j) * r.toNat, ?_, ?_⟩⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * j)) (show r.toNat + 1 ≤ 2 ^ 64 from r.isLt)
    rw [pow64_succ]; rw [Nat.mul_add, Nat.mul_one] at this; omega
  · rw [hc', hc, hI.mem]
    simp only [wv]
    rw [pow64_succ]
    grind

/-- `cmpLoop` from the carry flag set: the carry flag ends clear iff `X < N`
for the `w`-word numbers at `x16` and `x17`. -/
theorem cmpLoop_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eN) (h14 : s.gpr .x14 = BitVec.ofNat 64 w)
    (hc : s.c = true) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) :
    WP isa cmpLoop s fun t =>
      t.c = !decide (wv s.mem B eX w < wv s.mem B eN w) ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have h0 : CmpInv s B Z eX eN 0 s :=
    ⟨hs, Keep.refl _ _, rfl, by rw [h16]; rfl, by rw [h17]; rfl, ⟨0, Nat.one_pos, by rw [hc]; rfl⟩⟩
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (CmpInv s B Z eX eN)
    (fun j hj t hI _ => cmpStep_ok hX hN hj hI) h0 h14) fun t hI => ?_
  obtain ⟨d, hd, hval⟩ := hI.val
  refine ⟨?_, hI.mem, hI.keep⟩
  rw [← lt_of_borrow hd hval, Bool.not_not]

end VG.Proof.Bignum.AArch64
