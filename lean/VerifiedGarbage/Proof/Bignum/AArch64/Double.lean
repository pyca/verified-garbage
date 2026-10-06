import VerifiedGarbage.Proof.Bignum.AArch64.Mont

/-!
# Multiword arithmetic on AArch64: doubling modulo `m`

`double mo acc tmp o` doubles `[o] < m` into the accumulator (`w + 1`
words), a chain of `adcs` with the carry in the carry flag from word to
word, then subtracts `m` as Montgomery multiplication does (`subMod`,
`selectAcc`): `[o] := 2 [o] mod m` (`double_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- An addition with carry (`adcs`), as numbers. -/
theorem adcs_toNat (a b : BitVec 64) (c : Bool) :
    (a + b + BitVec.ofNat 64 c.toNat).toNat + 2 ^ 64 *
      (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc1 := Bool.toNat_le c
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- After `j` words of `double`'s loop from `s₀`: `D_j + 2^(64 j) c = 2 O_j`
for the low `j` words `D_j` of the accumulator, `O_j` of `[o]`, and the
carry `c` in the carry flag. -/
structure DblInv (s₀ : State) (B : Addr) (Z eA eo : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eo + 8 * j)
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * t.c.toNat = 2 * wv s₀.mem B eo j

theorem dblStep_ok {s₀ : State} {B : Addr} {Z w eA eo : Nat} (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eo ∨ eo + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State}
    (hI : DblInv s₀ B Z eA eo j t) :
    WP isa (.block ([ld .x3 .x17, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x17, next .x16] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      DblInv s₀ B Z eA eo (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (word t.mem B (eo + 8 * j) + word t.mem B (eo + 8 * j) +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eo + 8 * j)).toNat + (word t.mem B (eo + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eo + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hy : word t.mem B (eo + 8 * j) = word s₀.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc', hc]
    have hs := adcs_toNat (word t.mem B (eo + 8 * j)) (word t.mem B (eo + 8 * j)) t.c
    rw [hy] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hy]
    grind

/-- `[o] := 2 [o] mod m`, for `[o] < m`. -/
theorem double_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (double mo acc tmp o) s fun t =>
      wv t.mem B (slot w o) w = 2 * wv s.mem B (slot w o) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  unfold double
  refine WP.seq (WP.mono (WP.keep [.x3, .x5, .x6, .x7, .x8, .x10, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x5 = off B (slot w o) ∧ t.gpr .x10 = off B (slot w mo) ∧ t.gpr .x8 = off B (slot w acc) ∧
      t.gpr .x6 = off B (slot w tmp) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.gpr .x17 = off B (slot w o) ∧ t.gpr .x16 = off B (slot w acc) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.c = false ∧ t.mem = s.mem)
    (by brun [h0, hdr_enc (sa o ho), hdr_enc (sa mo hmo), hdr_enc (sa acc hacc), hdr_enc (sa tmp htmp),
      hdr_enc (show sW < 32 by decide), hl _ (sa o ho), hl _ (sa mo hmo), hl _ (sa acc hacc),
      hl _ (sa tmp htmp), hl sW (by decide), hH.harr o ho, hH.harr mo hmo, hH.harr acc hacc,
      hH.harr tmp htmp, hH.hw]) rfl rfl rfl)
    fun s₁ ⟨⟨h5, h10, h8, h6, h12, h7, h17, h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0' : DblInv s₁ B Z (slot w acc) (slot w o) 0 s₁ :=
    ⟨hs₁, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (DblInv s₁ B Z (slot w acc) (slot w o))
    (fun j hj t hI _ => dblStep_ok (by have := sl acc hacc; omega) (by have := sl o ho; omega)
      (by have := sp (Ne.symm d3); omega) hj hI) h0' h14) fun s₂ hI => ?_)
  have hval := hI.val
  have s₂7 : s₂.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w acc + 8 * w)) (BitVec.ofNat 64 s₂.c.toNat))
    (by brun [hI.x16, s₂7, hI.scr.st (show slot w acc + 8 * w + 8 ≤ Z by have := sl acc hacc; omega)]
        simp only [add_zero64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨hm₃, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.wr
  have k13 := (hI.keep.trans k₃)
  have o3 : Outside B (slot w acc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [writeW_outside s₂.mem B _ (by have := sl acc hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3
  have fN : wv s₃.mem B (slot w mo) w = wv s.mem B (slot w mo) w :=
    o3.wv (by have := sp (Ne.symm d1); omega) (by have := sl mo hmo; omega)
  have fO : wv s₁.mem B (slot w o) w = wv s.mem B (slot w o) w := by rw [hm₁]
  have hTl : wv s₃.mem B (slot w acc) w = wv s₂.mem B (slot w acc) w := by
    rw [hm₃]; exact (writeW_outside s₂.mem B _ (by have := sl acc hacc; omega)).wv (Or.inl (by omega))
      (by have := sl acc hacc; omega)
  have hTw : (word s₃.mem B (slot w acc + 8 * w)).toNat = s₂.c.toNat := by
    rw [hm₃, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le s₂.c; omega)]
  have k1 := k₁.trans k13
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr .x8 (by decide)).trans h8) ((k13.gpr .x10 (by decide)).trans h10)
    ((k13.gpr .x6 (by decide)).trans h6) ((k13.gpr .x12 (by decide)).trans h12)
    ((k13.gpr .x7 (by decide)).trans h7) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₄ ⟨c', hc₄, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.wr
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr .x8 (by decide)).trans h8) ((k14.gpr .x6 (by decide)).trans h6)
    ((k14.gpr .x5 (by decide)).trans h5) ((k14.gpr .x12 (by decide)).trans h12) hc₄ (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (slot w acc) w = wv s₃.mem B (slot w acc) w :=
    ho₄.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  rw [fN] at hD
  rw [fO] at hval
  have hN0 : 0 < wv s.mem B (slot w mo) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w acc) w) (Tw := s₂.c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (slot w tmp) w) (m := wv s.mem B (slot w mo) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : s₂.c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [acc, tmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [acc, tmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

end VG.Proof.Bignum.AArch64
