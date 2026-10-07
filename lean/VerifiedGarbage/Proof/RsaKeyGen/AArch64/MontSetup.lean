import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.RsaKeyGen.MrMont

/-!
# A candidate on AArch64: Montgomery arithmetic modulo `c`

`montSetup` (`montSetup_ok`): `-c⁻¹ mod 2^64` into the header (`msHead_ok`),
the number 1 (`aOne`), `R² mod c` (`aR2`, `vg_rsa_public_precompute`'s
`r2Steps`, `r2_ok`), `R mod c` (`aY`, then `aR1`), `c − R mod c` (`aRm1`)
and the number of uniform witnesses needed, `checksW w` (`kChecks`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

/-- `-c⁻¹` into `sMinv`, then `x12 := w`, `x9 := 1`, `x13 := 0`. -/
theorem msHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hodd : (word s.mem B (slot w aN)).toNat % 2 = 1) :
    WP isa (.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1,
      movi .x13 0])) s fun t =>
      (((word s.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
        t.mem = s.mem.writeW (off B (8 * sMinv)) (word t.mem B (8 * sMinv)) ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x9 = 1 ∧ t.gpr .x13 = 0) ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have sN := h.sl (show aN < 16 by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8, .x3] (Q := fun t => t.gpr .x3 = word s.mem B (slot w aN) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show sArr aN < 32 by decide), hs.ld (d := 8 * sArr aN) (by simp only [sArr, aN]; omega),
      h.harr aN (by decide), hs.ld (d := slot w aN) (by omega)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h3, m₁⟩, k₁⟩ => ?_
  refine WP.mono (minv_ok s₁ (by rw [h3]; exact hodd)) fun s₂ ⟨hinv, k₂, m₂⟩ => ?_
  have k12 := k₁.trans k₂
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have hs₂ := hs.congr k12.wr
  refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t => t.mem = s₂.mem.writeW (off B (8 * sMinv)) (s₂.gpr .x15) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x9 = 1 ∧ t.gpr .x13 = 0) (by
    have hW : (s₂.mem.writeW (off B (8 * sMinv)) (s₂.gpr .x15)).readW (off B (8 * sW)) 64 = BitVec.ofNat 64 w := by
      rw [← h.hw, m₂, m₁]; exact (writeW_outside _ _ _ (by simp only [sMinv]; omega)).word
        (by simp only [sMinv, sW]; omega) (by simp only [sW]; omega)
    brun [h0₂, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₂.st (d := 8 * sMinv) (by simp only [sMinv]; omega), hs₂.ld (d := 8 * sW) (by simp only [sW]; omega), hW])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hm, h12, h9, h13⟩, k₃⟩ => ?_
  have hM : word t.mem B (8 * sMinv) = s₂.gpr .x15 := by rw [hm]; exact word_writeW_self _ _ _ _
  refine ⟨⟨by rw [hM, ← h3]; exact hinv, by rw [hM, hm, m₂, m₁], h12, h9, h13⟩, (k12.trans k₃).mono (by decide)⟩

/-- The chain of selections of `checksW`. -/
theorem checks_sel {w : Nat} (hw : w ≤ 64) :
    (if decide (59 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 3) else
      if decide (22 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 4) else
      if decide (8 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 5) else
      if decide (7 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 6) else
      if decide (6 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 7) else
      if decide (5 ≤ w) = true then BitVec.setWidth 64 (BitVec.ofNat 16 8) else
      BitVec.setWidth 64 (BitVec.ofNat 16 27)) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w) := by
  have key : ∀ w < 65, (if decide (59 ≤ w) = true then 3 else if decide (22 ≤ w) = true then 4 else
      if decide (8 ≤ w) = true then 5 else if decide (7 ≤ w) = true then 6 else
      if decide (6 ≤ w) = true then 7 else if decide (5 ≤ w) = true then 8 else 27) =
      VG.Proof.RsaKeyGen.checksW w := by decide
  rw [← key w (by omega)]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- The number of uniform witnesses needed into `kChecks`. -/
theorem msChecks_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hw64 : w ≤ 64) :
    WP isa (.block ([ldh .x12 sW, movi .x5 27] ++ checksIf 5 8 ++ checksIf 6 7 ++ checksIf 7 6 ++ checksIf 8 5 ++
      checksIf 22 4 ++ checksIf 59 3 ++ [sth .x5 kChecks])) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kChecks)) (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w)) ∧
        Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  refine WP.mono (WP.keep [.x12, .x5, .x4, .x3, .x6] (Q := fun t =>
      t.mem = s.mem.writeW (off B (8 * kChecks)) (BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w))) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨hm, k.mono (by decide)⟩
  have hwn : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  brun [checksIf, h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show kChecks < 32 by decide),
    hs.ld (d := 8 * sW) (by simp only [sW]; omega), hs.st (d := 8 * kChecks) (by simp only [kChecks, kE, sFn]; omega),
    h.hw, subs_carry]
  simp only [hwn, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  rw [checks_sel hw64]

/-- What `montSetup` changes after `-c⁻¹`. -/
def msTail (w : Nat) : List (Nat × Nat) :=
  [(slot w aOne, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aR2, 8 * (w + 2)), (8 * sCnt, 8), (slot w aY, 8 * (w + 2)), (slot w aR1, 8 * (w + 2)),
    (slot w aRm1, 8 * (w + 2)), (8 * kChecks, 8)]

/-- What `montSetup` changes. -/
def msRanges (w : Nat) : List (Nat × Nat) := (8 * sMinv, 8) :: msTail w

theorem msRanges_mut (w : Nat) : ∀ r ∈ msRanges w, KMut r := by
  simp only [msRanges, msTail, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | exact KMut.ofSlot w _ _ | exact KMut.hdr (by decide)

theorem msTail_mut (w : Nat) : ∀ r ∈ msTail w, KMut r :=
  fun r hr => msRanges_mut w r (List.mem_cons_of_mem _ hr)

/-- Disjointness of a range from each of a list of literal ranges of the
working space. -/
macro "ms_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, msTail, r2Ranges, slot,
    hdrBytes, aN, aAcc, aTmp, aR2, aY, aOne, aR1, aRm1, sCnt, kChecks, kE, sFn, sMinv]
  and_intros <;> omega))

/-- `msTail` keeps `-c⁻¹` and `c`. -/
theorem ms_fix {B : Addr} {Z w : Nat} {m m' : Mem} (f : Frm B (msTail w) m m') (hz : B.toNat + Z ≤ 2 ^ 64)
    (hZ : slot w 16 ≤ Z) :
    word m' B (8 * sMinv) = word m B (8 * sMinv) ∧ word m' B (slot w aN) = word m B (slot w aN) ∧
      wv m' B (slot w aN) w = wv m B (slot w aN) w := by
  simp only [slot, hdrBytes] at hZ
  refine ⟨f.word_eq (by ms_disj) (by simp only [sMinv]; omega), f.word_eq (by ms_disj) (by simp only [slot, hdrBytes, aN]; omega),
    f.wv_eq (by ms_disj) (by simp only [slot, hdrBytes, aN]; omega)⟩

/-- `montSetup`: `-c⁻¹`, `R² mod c`, `R mod c`, `c − R mod c` and `checksW w`. -/
theorem montSetup_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w) (hw4 : 4 ≤ w)
    (hw64 : w ≤ 64) (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (htop : 2 ^ (64 * w - 1) ≤ N) :
    WP isa (seqs (montSetup M.mm)) s fun t => Ws t B Z w ∧
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.checksW w) ∧
      Frm B (msRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hZ16 : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hZ8 : slot w 8 ≤ Z := h.good.2
  have hw2 := h.w2
  have hw' : w < 2 ^ 31 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hNlt : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  have hN1 : 1 < N := by
    have : 2 ≤ 2 ^ (64 * w - 1) := by
      rw [show 64 * w - 1 = (64 * w - 2) + 1 by omega, Nat.pow_succ]; have := Nat.two_pow_pos (64 * w - 2); omega
    omega
  have hlo : 2 ^ (64 * (w - 1)) ≤ N := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) htop
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem B (slot w aN) 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega, hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega
  simp only [montSetup, List.append_assoc]
  refine wp_seqs_append (a := [_, _]) (by simp) (by simp [r2Steps]) ?_
  simp only [seqs]
  -- `-c⁻¹`, and 1.
  refine WP.seq (WP.mono (msHead_ok h hodd0) fun s₁ ⟨⟨hinv₁, hm₁, h12₁, h9₁, h13₁⟩, k₁⟩ => ?_)
  obtain ⟨mi, hmi⟩ : ∃ mi, word s₁.mem B (8 * sMinv) = mi := ⟨_, rfl⟩
  rw [hmi] at hinv₁ hm₁
  have o₁ : Outside B (8 * sMinv) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega)
  have f₁ : Frm B (msRanges w) s.mem s₁.mem := Frm.of_outside o₁ (by simp [msRanges])
  have h₁ : Ws s₁ B Z w := h.congr' f₁ (msRanges_mut w) k₁ (by decide)
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [o₁.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)]; exact hn
  have hw₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) :=
    o₁.word (by simp only [slot, hdrBytes, aN, sMinv]; omega) (by simp only [slot, hdrBytes, aN]; omega)
  rw [← hw₁] at hinv₁
  have g₁ : Good s₁ B Z w mi := hmi ▸ h₁.good.1
  refine WP.mono (setWord_ok g₁.scr g₁.x0 g₁.hdr hZ8 h12₁ hw' (o := aOne) (by decide) (i := 0) (by omega)
    (by rw [h13₁]; rfl)) fun s₂ ⟨hv₂, o₂, k₂⟩ => ?_
  rw [h9₁] at hv₂
  have F₂ : Frm B (msTail w) s₁.mem s₂.mem := Frm.of_outside o₂ (by simp [msTail])
  have h₂ : Ws s₂ B Z w := h₁.congr' F₂ (msTail_mut w) k₂ (by decide)
  obtain ⟨e₂, w₂, n₂⟩ := ms_fix F₂ hnw hZ
  have g₂ : Good s₂ B Z w mi := by have := h₂.good.1; rwa [e₂, hmi] at this
  -- `R² mod c`.
  refine wp_seqs_append (by simp [r2Steps]) (by simp) ?_
  refine WP.mono (r2_ok M g₂ hZ8 (by omega) (by omega) (n₂.trans hn₁) (by rw [w₂]; exact hinv₁) hodd hlo)
    fun s₃ ⟨g₃, hlt₃, hr₃, fr₃, k₃⟩ => ?_
  have F₃ : Frm B (msTail w) s₁.mem s₃.mem := F₂.trans (fr₃.mono (by simp [r2Ranges, msTail]))
  have k13 := k₂.trans k₃
  have h₃ : Ws s₃ B Z w := h₁.congr' F₃ (msTail_mut w) k13 (by decide)
  obtain ⟨e₃, w₃, n₃⟩ := ms_fix F₃ hnw hZ
  have hR2₃ : wv s₃.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [← hr₃, Nat.mod_eq_of_lt hlt₃]
  have hone₃ : wv s₃.mem B (slot w aOne) w = 1 := by
    rw [fr₃.wv_eq (by ms_disj) (by simp only [slot, hdrBytes, aOne]; omega), hv₂]; rfl
  -- `R mod c`.
  refine wp_seqs_append (by simp) (by simp [subA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (M.mm_ok g₃ hZ8 (by omega) hw' (o := aY) (a := aR2) (b := aOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [w₃]; exact hinv₁)
    (by rw [hone₃, n₃, hn₁]; exact hN1)) fun s₄ ⟨g₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_)
  rw [n₃, hn₁, hR2₃, hone₃] at hy₄
  rw [n₃, hn₁] at hlt₄
  have hY : wv s₄.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt₄]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy₄, Nat.mul_one, Nat.mod_mod]
  have fa₄ : Frm B (msTail w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [msTail])
  have F₄ : Frm B (msTail w) s₁.mem s₄.mem := F₃.trans fa₄
  have k14 := k13.trans k₄
  have h₄ : Ws s₄ B Z w := h₁.congr' F₄ (msTail_mut w) k14 (by decide)
  have hR2₄ : wv s₄.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hR2₃
  -- `[aR1] := R mod c`.
  refine WP.mono (copyA_ok h₄ (o := aR1) (a := aY) (by decide) (by decide) (by decide))
    fun s₅ ⟨hv₅, o₅, _, _, k₅⟩ => ?_
  rw [hY] at hv₅
  have fo₅ : Frm B (msTail w) s₄.mem s₅.mem :=
    Frm.of_outside (o₅.mono (o' := slot w aR1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [msTail])
  have F₅ : Frm B (msTail w) s₁.mem s₅.mem := F₄.trans fo₅
  have k15 := k14.trans k₅
  have h₅ : Ws s₅ B Z w := h₁.congr' F₅ (msTail_mut w) k15 (by decide)
  obtain ⟨e₅, w₅, n₅⟩ := ms_fix F₅ hnw hZ
  have hR2₅ : wv s₅.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₅.wv (by simp only [slot, hdrBytes, aR1, aR2]; omega) (by simp only [slot, hdrBytes, aR2]; omega)]; exact hR2₄
  -- `[aRm1] := c − R mod c`.
  refine wp_seqs_append (by simp [subA]) (by simp) ?_
  refine WP.mono (subA_ok h₅ (o := aRm1) (a := aN) (b := aR1) (by decide) (by decide) (by decide) (.inr (by decide))
    (by decide)) fun s₆ ⟨hv₆, o₆, _, _, _, k₆⟩ => ?_
  rw [hv₅, n₅, hn₁] at hv₆
  have hRm₆ : wv s₆.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N := by
    have hx := wv_lt s₆.mem B (slot w aRm1) w
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega)
    cases hb : (!s₆.c) <;> rw [hb] at hv₆ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero] at hv₆ <;> omega
  have fo₆ : Frm B (msTail w) s₅.mem s₆.mem :=
    Frm.of_outside (o₆.mono (o' := slot w aRm1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [msTail])
  have F₆ : Frm B (msTail w) s₁.mem s₆.mem := F₅.trans fo₆
  have k16 := k15.trans k₆
  have h₆ : Ws s₆ B Z w := h₁.congr' F₆ (msTail_mut w) k16 (by decide)
  have hR2₆ : wv s₆.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [o₆.wv (by simp only [slot, hdrBytes, aRm1, aR2]; omega) (by simp only [slot, hdrBytes, aR2]; omega)]; exact hR2₅
  have hR1₆ : wv s₆.mem B (slot w aR1) w = 2 ^ (64 * w) % N := by
    rw [o₆.wv (by simp only [slot, hdrBytes, aRm1, aR1]; omega) (by simp only [slot, hdrBytes, aR1]; omega)]; exact hv₅
  -- `checksW w`.
  rw [seqs_one]
  refine WP.mono (msChecks_ok h₆ hw64) fun t ⟨hm, k₇⟩ => ?_
  have o₇ : Outside B (8 * kChecks) 8 s₆.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [kChecks, kE, sFn]; omega)
  have F₇ : Frm B (msTail w) s₁.mem t.mem := F₆.trans (Frm.of_outside o₇ (by simp [msTail]))
  have k17 := k16.trans k₇
  obtain ⟨e₇, w₇, n₇⟩ := ms_fix F₇ hnw hZ
  have hk8 : 8 * kChecks + 8 ≤ 256 := by decide
  have kc : ∀ j, j < 16 → wv t.mem B (slot w j) w = wv s₆.mem B (slot w j) w := fun j hj =>
    o₇.wv (Or.inr (Nat.le_trans hk8 (Nat.le_add_right _ _))) (by have := slot_lt (w := w) hj; omega)
  refine ⟨h₁.congr' F₇ (msTail_mut w) k17 (by decide), by rw [w₇, e₇, hmi]; exact hinv₁, n₇.trans hn₁,
    ?_, ?_, ?_, by rw [hm]; exact word_writeW_self _ _ _ _,
    f₁.trans (F₇.mono fun r hr => List.mem_cons_of_mem _ hr), (k₁.trans k17).mono (by decide)⟩
  · rw [kc aR2 (by decide)]; exact hR2₆
  · rw [kc aR1 (by decide)]; exact hR1₆
  · rw [kc aRm1 (by decide)]; exact hRm₆

end VG.Proof.RsaKeyGen.AArch64
