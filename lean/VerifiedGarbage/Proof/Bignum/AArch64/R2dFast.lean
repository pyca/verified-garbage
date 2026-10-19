module
public import VerifiedGarbage.Impl.Bignum.AArch64.R2Div
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.R2

import VerifiedGarbage.Proof.Bignum.AArch64.R2dStep
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `R² mod m` by long division on AArch64

`steps` runs `step` `c` times, counted in slot `sCnt` (`r2dSteps_ok`): `x 2^(64 c) mod m`.
`fast` sets `x := R - m`, `v`, and runs `w` steps (`r2dFast_ok`): `R² mod m`, for
`m` odd with its top bit set. `choice old` takes `fast` for those and `old`
otherwise (`r2dChoice_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero eval_nonzero eq_zero_iff)

/-- `sqs`' count: the count `c ≥ 1` in slot `sCnt` less one, there and in `x13`. -/
theorem sqCount_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 64)
    (hcnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 c) :
    WP isa (.block (dblCount sCnt)) t fun t' => Good t' B Z w minv ∧
      word t'.mem B (8 * sCnt) = BitVec.ofNat 64 (c - 1) ∧ t'.gpr .x13 = BitVec.ofNat 64 (c - 1) ∧
      Outside B (8 * sCnt) 8 t.mem t'.mem ∧ Keep [.x13] t t' := by
  have hn := hg.scr.nowrap
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  have hld : InRegions (t.rd ++ t.wr) (off B (8 * sCnt)) 8 := hg.scr.ld (by have := hhs 8; omega)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.mem = t.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (c - 1)) ∧ t'.gpr .x13 = BitVec.ofNat 64 (c - 1)) (by
    brun [hg.x0, hdr_enc (show sCnt < 32 by decide), hld,
      hg.scr.st (show 8 * sCnt + 8 ≤ Z by have := hhs 8; omega), hcnt, ofNat_sub_one' hc hc']) rfl rfl rfl) fun t' ⟨⟨hm', h13'⟩, k'⟩ => ?_
  exact ⟨⟨hg.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hg.x0,
    by rw [hm']; exact Hdr.store hg.hdr (by decide) (by decide) _⟩, by rw [hm', word_writeW_self], h13',
    by rw [hm']; exact writeW_outside _ _ _ (by have := hhs 8; omega), k'⟩

/-! ## The steps -/

theorem eval_count {t : State} {j c : Nat} (hj : j < c) (h : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) :
    isa.eval (.nonzero .x .x13) t = some (decide (j + 1 < c)) := by
  rw [eval_nonzero]
  congr 1
  by_cases hc : j + 1 < c
  · have hne : t.gpr .x13 ≠ 0 := fun e => by
      rw [e] at h; exact absurd (h.mpr (by omega)) (by simp)
    rw [bne_iff_ne.mpr hne, decide_eq_true hc]
  · have he : t.gpr .x13 = 0 := BitVec.eq_of_toNat_eq (by
      by_contra hne; exact (h.mp (by simpa using hne)) (by omega))
    rw [he, decide_eq_false hc]; rfl


/-- After `j` of `steps`' `c` steps from `s`, which started at `x = X₀`. -/
structure R2dStepsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (M D X0 c j : Nat) (t : State) :
    Prop where
  g : Good t B Z w minv
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  x : wv t.mem B (slot w aR2) w = X0 * 2 ^ (64 * j) % M
  n : wv t.mem B (slot w aN) w = M
  top : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = D
  v : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64
  frm : Frm B (r2Ranges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem stepsIter_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D X0 c j : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hd : 2 ^ 63 ≤ D) (hM0 : 0 < M) (hc' : c < 2 ^ 31)
    (hj : j < c) (hI : R2dStepsInv s B Z w minv M D X0 c j t) :
    WP isa (.seq step (.block (dblCount sCnt))) t fun t' =>
      R2dStepsInv s B Z w minv M D X0 c (j + 1) t' ∧ ((t'.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) := by
  have hn := hI.g.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  have sNA := slot_sep (w := w) (show aN ≠ aAcc by decide)
  have sNX := slot_sep (w := w) (show aN ≠ aR2 by decide)
  have sTA := slot_sep (w := w) (show aTmp ≠ aAcc by decide)
  have sTX := slot_sep (w := w) (show aTmp ≠ aR2 by decide)
  have lN := sl8 aN (by decide)
  have lT := sl8 aTmp (by decide)
  refine WP.seq (WP.mono (r2dStep_ok hI.g hZ hw hw' hI.n hI.top hd hI.v (by rw [hI.x]; exact Nat.mod_lt _ hM0))
    fun t₁ ⟨g₁, x₁, a₁, k₁⟩ => ?_)
  have hcnt₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [a₁.word_eq (fun j' hj' => Or.inl (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl <;> exact hhs _)) (by have := hhs 8; omega), hI.cnt]
  have arrs : ∀ j' ∈ [aAcc, aR2], ∀ d k, (d + 8 * k ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w j' ∨ slot w j' + 8 * (w + 2) ≤ d) := by
    intro j' hj' d k h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · exact h1
    · exact h2
  refine WP.mono (sqCount_ok g₁ hZ (c := c - j) (by omega) (by omega) hcnt₁)
    fun t' ⟨g', c', h13', o', k'⟩ => ⟨?_, by rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega⟩
  have hN₁ : wv t₁.mem B (slot w aN) w = M := by
    rw [a₁.wv_eq (fun j' hj' => arrs j' hj' _ _ (by omega) (by omega)) (by omega), hI.n]
  have hT₁ : word t₁.mem B (slot w aN + 8 * (w - 1)) = word t.mem B (slot w aN + 8 * (w - 1)) :=
    a₁.word_eq (fun j' hj' => arrs j' hj' _ 1 (by omega) (by omega)) (by omega)
  have hV₁ : word t₁.mem B (slot w aTmp) = word t.mem B (slot w aTmp) :=
    a₁.word_eq (fun j' hj' => arrs j' hj' _ 1 (by omega) (by omega)) (by omega)
  refine ⟨g', by rw [c', show c - j - 1 = c - (j + 1) by omega], ?_, ?_, ?_, ?_, ?_,
    ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs aR2; omega) (by have := sl8 aR2 (by decide); omega), x₁, hI.x, Nat.mod_mul_mod,
      Nat.mul_assoc, ← Nat.pow_add, show 64 * j + 64 = 64 * (j + 1) by omega]
  · rw [o'.wv (by have := hhs aN; omega) (by omega), hN₁]
  · rw [o'.word (by have := hhs aN; omega) (by omega), hT₁, hI.top]
  · rw [o'.word (by have := hhs aTmp; omega) (by omega), hV₁, hI.v]
  · exact (hI.frm.trans (Frm.of_arrays a₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges]))

/-- `steps`' start: the count `c` (in `x13`) into slot `sCnt`. -/
theorem r2dStepsStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D c : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (h13 : s.gpr .x13 = BitVec.ofNat 64 c) (hM : wv s.mem B (slot w aN) w = M)
    (hD : (word s.mem B (slot w aN + 8 * (w - 1))).toNat = D)
    (hv : (word s.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv s.mem B (slot w aR2) w < M) :
    WP isa (.block [sth .x13 sCnt]) s (R2dStepsInv s B Z w minv M D (wv s.mem B (slot w aR2) w) c 0) := by
  have hn := hg.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCnt)) (s.gpr .x13))
    (by brun [hg.x0, hdr_enc (show sCnt < 32 by decide), hg.scr.st (show 8 * sCnt + 8 ≤ Z by have := hhs 8; omega)])
    rfl rfl rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sCnt) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by have := hhs 8; omega)
  exact ⟨⟨hg.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0,
      by rw [hm₁]; exact Hdr.store hg.hdr (by decide) (by decide) _⟩,
      by rw [hm₁, word_writeW_self, h13, Nat.sub_zero],
      by rw [o₁.wv (by have := hhs aR2; omega) (by have := sl8 aR2 (by decide); omega), Nat.mul_zero, Nat.pow_zero,
        Nat.mul_one, Nat.mod_eq_of_lt hX],
      by rw [o₁.wv (by have := hhs aN; omega) (by have := sl8 aN (by decide); omega), hM],
      by rw [o₁.word (by have := hhs aN; omega) (by have := sl8 aN (by decide); omega), hD],
      by rw [o₁.word (by have := hhs aTmp; omega) (by have := sl8 aTmp (by decide); omega), hv],
      Frm.of_outside o₁ (by simp [r2Ranges]), k₁.mono (by decide)⟩

/-- `steps`: `c ≥ 1` steps (`c` in `x13`), `x := x 2^(64 c) mod m`. -/
theorem r2dSteps_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M D c : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hd : 2 ^ 63 ≤ D) (hc : 1 ≤ c) (hc' : c < 2 ^ 31)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 c) (hM : wv s.mem B (slot w aN) w = M)
    (hD : (word s.mem B (slot w aN + 8 * (w - 1))).toNat = D)
    (hv : (word s.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / D - 2 ^ 64)
    (hX : wv s.mem B (slot w aR2) w < M) :
    WP isa steps s (R2dStepsInv s B Z w minv M D (wv s.mem B (slot w aR2) w) c c) := by
  have hM0 : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hX
  unfold steps
  exact WP.seq (WP.mono (r2dStepsStart_ok hg hZ h13 hM hD hv hX) fun s₁ h₀ =>
    count_loop (n := c) (by omega) _ (fun j hj t hI => stepsIter_ok hZ hw hw' hd hM0 hc' hj hI) h₀)

/-! ## `R² mod m` -/

/-- `(R - m) R ≡ R R (mod m)`. -/
theorem neg_mul_mod {R M : Nat} (h : M ≤ R) : (R - M) * R % M = R * R % M := by
  have e : R * R = (R - M) * R + M * R := by rw [← Nat.add_mul, Nat.sub_add_cancel h]
  rw [e, Nat.add_mul_mod_self_left]

/-- `fast`: `R² mod m` into array `aR2`, for the odd `m` of `w ≥ 2` words
whose top bit is set. -/
theorem r2dFast_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {M : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hM : wv s.mem B (slot w aN) w = M) (hodd : M % 2 = 1)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat) :
    WP isa fast s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < M ∧ wv t.mem B (slot w aR2) w % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega)
  have sXN := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have sTN := slot_sep (w := w) (show aTmp ≠ aN by decide)
  have sTX := slot_sep (w := w) (show aTmp ≠ aR2 by decide)
  have lN := sl8 aN (by decide)
  have lX := sl8 aR2 (by decide)
  have lT := sl8 aTmp (by decide)
  have hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (by decide)
  -- `m ≥ 2^(64 w - 1)`, and odd, so `R - m < m`.
  have hMB : M < 2 ^ (64 * w) := hM ▸ wv_lt _ _ _ _
  have hMw := wv_split1 s.mem B (slot w aN) (show 1 ≤ w by omega)
  rw [hM] at hMw
  have hP : 2 ^ (64 * w) = 2 ^ (64 * (w - 1)) * 2 ^ 63 * 2 := by
    rw [Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
  have hlo : 2 ^ (64 * (w - 1)) * 2 ^ 63 ≤ M := by
    rw [hMw, Nat.mul_comm (2 ^ (64 * (w - 1)))]
    exact Nat.le_trans (Nat.mul_le_mul_right _ hd) (Nat.le_add_right _ _)
  have hlt : 2 ^ (64 * w) - M < M := by
    have h2 : 2 ^ (64 * (w - 1)) * 2 ^ 63 % 2 = 0 := by
      rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 from rfl, Nat.mul_zero, Nat.zero_mod]
    have : M ≠ 2 ^ (64 * (w - 1)) * 2 ^ 63 := fun h => by rw [h] at hodd; omega
    omega
  unfold fast
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x6, .x7, .x9, .x11, .x12] (Q := fun t =>
    t.gpr .x11 = off B (slot w aR2) ∧ t.gpr .x9 = off B (slot w aN) ∧ t.gpr .x6 = off B (slot w aTmp) ∧
    t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aR2 < 32 by decide),
        hdr_enc (show sArr aTmp < 32 by decide), hdr_enc (show sW < 32 by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide),
        hg.hdr.harr aR2 (by decide), hg.hdr.harr aTmp (by decide), hg.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h11, h9, h6, h12, h7, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  -- `x := R - m`.
  refine WP.seq (WP.mono (r2dNeg_ok hs₁ h11 h9 h12 h7 (by omega) hw' (by omega) (by omega) (by omega))
    fun t₂ ⟨b, hv₂, o₂, k₂⟩ => ?_)
  rw [hm₁, hM] at hv₂
  have hb : b = true := by
    cases b
    · simp only [Bool.toNat_false, Nat.mul_zero] at hv₂; omega
    · rfl
  subst hb
  rw [Bool.toNat_true, Nat.mul_one] at hv₂
  have hs₂ := hs₁.congr k₂.wr
  have N₂ : wv t₂.mem B (slot w aN) w = M := by rw [o₂.wv (by omega) (by omega), hm₁, hM]
  have D₂ : word t₂.mem B (slot w aN + 8 * (w - 1)) = word s.mem B (slot w aN + 8 * (w - 1)) := by
    rw [o₂.word (by omega) (by omega), hm₁]
  -- `v`.
  refine WP.seq (WP.mono (r2dRecip_ok hs₂ ((k₂.gpr .x9 (by decide)).trans h9) ((k₂.gpr .x12 (by decide)).trans h12)
    ((k₂.gpr .x6 (by decide)).trans h6) ((k₂.gpr .x7 (by decide)).trans h7) (by omega) hw' (by omega) (by omega)
    (by rw [D₂]; exact hd)) fun t₃ ⟨hv₃, o₃, k₃⟩ => ?_)
  rw [D₂] at hv₃
  have a₃ : Arrays B w [aR2, aTmp] s.mem t₃.mem := by
    rw [← hm₁]
    exact (Arrays.of_outside (j := aR2) (by decide) o₂ (Nat.le_refl _) (by omega)).trans
      (Arrays.of_outside (j := aTmp) (by decide) o₃ (Nat.le_refl _) (by omega))
  have hs₃ := hs₂.congr k₃.wr
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.seq (WP.mono (WP.keep [.x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 w ∧ t.mem = t₃.mem)
    (by brun [(k13.gpr .x0 (by decide)).trans hg.x0, hdr_enc (show sW < 32 by decide),
        hs₃.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
        (a₃.hdr hg.hdr).hw]) (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨h13, hm₄⟩, k₄⟩ => ?_)
  have g₄ : Good t₄ B Z w minv :=
    ⟨hs₃.congr k₄.wr, ((k13.trans k₄).gpr .x0 (by decide)).trans hg.x0, by rw [hm₄]; exact a₃.hdr hg.hdr⟩
  have sep : ∀ j ∈ [aR2, aTmp], ∀ d k, (d + 8 * k ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w aTmp ∨ slot w aTmp + 8 * (w + 2) ≤ d) →
      (d + 8 * k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d) := by
    intro j hj d k h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact h1
    · exact h2
  have X₃ : wv t₃.mem B (slot w aR2) w = 2 ^ (64 * w) - M := by
    rw [o₃.wv (by omega) (by omega)]; omega
  refine WP.mono (r2dSteps_ok g₄ hZ hw hw' hd (by omega) hw' h13
    (by rw [hm₄, a₃.wv_eq (fun j hj => sep j hj _ _ (by omega) (by omega)) (by omega), hM])
    (by rw [hm₄, a₃.word_eq (fun j hj => sep j hj _ 1 (by omega) (by omega)) (by omega)])
    (by rw [hm₄]; exact hv₃) (by rw [hm₄, X₃]; exact hlt)) fun t hI => ?_
  rw [hm₄, X₃] at hI
  refine ⟨hI.g, by rw [hI.x]; exact Nat.mod_lt _ (by omega), by rw [hI.x, Nat.mod_mod, neg_mul_mod (by omega)], ?_,
    ((k13.trans k₄).trans hI.keep).mono (by decide)⟩
  refine (Frm.of_arrays a₃ (by simp [r2Ranges])).trans ?_
  rw [← hm₄]
  exact hI.frm

/-- `choice old`: `fast` if the top bit of `m` is set, `old` otherwise; both
start from `s`'s memory. -/
theorem r2dChoice_ok {old : Prog isa} {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {Q : State → Prop}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hold : ∀ t, Good t B Z w minv → t.mem = s.mem → Keep mmRegs s t →
      (word s.mem B (slot w aN + 8 * (w - 1))).toNat < 2 ^ 63 → WP isa old t Q)
    (hfast : ∀ t, Good t B Z w minv → t.mem = s.mem → Keep mmRegs s t →
      2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat → WP isa fast t Q) :
    WP isa (choice old) s Q := by
  have hs := hg.scr
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; have := slot_le (w := w) (show 7 < 8 by decide); omega)
  have lN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold choice
  refine WP.seq (WP.mono (WP.keep [.x3, .x9, .x12, .x13] (Q := fun t =>
    t.gpr .x3 = word s.mem B (slot w aN + 8 * (w - 1)) >>> 63 ∧ t.mem = s.mem)
    (by brun [fastTest, hg.x0, hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sW < 32 by decide),
        hl (sArr aN) (by decide), hl sW (by decide), hg.hdr.harr aN (by decide), hg.hdr.hw,
        shl3_sub8 hw (show w < 2 ^ 61 by omega), off_add, hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h3, hm₁⟩, k₁⟩ => ?_)
  have g₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, by rw [hm₁]; exact hg.hdr⟩
  rw [shr63_toNat] at h3
  by_cases h : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat
  · refine WP.ite false (by rw [eval_zero, h3, decide_eq_true h]; rfl) (by simp) fun _ => ?_
    exact hfast t₁ g₁ hm₁ (k₁.mono (by decide)) h
  · refine WP.ite true (by rw [eval_zero, h3, decide_eq_false h]; rfl) (fun _ => ?_) (by simp)
    exact hold t₁ g₁ hm₁ (k₁.mono (by decide)) (by omega)

end VG.Proof.Bignum.AArch64
