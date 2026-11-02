module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdProd
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: `b`, `b² - 4 n`

`square_ok`: `b = q + 1` (narrow array 6) and `b²` (wide array 6);
`minus4n_ok`: `b² - 4 n` (wide array 7), and its checks and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

theorem pidxS : PIdx nBy wB wSq wT := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `square`: `b = (q + 1) mod 2^(64 v)` (narrow array 6) and `b²` by `prodStep` (wide array 6). -/
theorem square_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {q : Nat}
    (hq : wv s.mem I.B (slot (vk I.k) nD) (vk I.k) = q)
    (one : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1) :
    WP isa square s fun t => G I m₀ (vk I.k) c t ∧
      wv t.mem I.B (slot (vk I.k) nB) (vk I.k) = (q + 1) % 2 ^ (64 * vk I.k) ∧
      wv t.mem I.B (slot (Wk I.k) wSq) (Wk I.k) = ((prodStep (64 * Wk I.k))^[64 * vk I.k]
        ((q + 1) % 2 ^ (64 * vk I.k), (q + 1) % 2 ^ (64 * vk I.k), 0)).2.2 ∧
      (∀ j k, j < 6 ∨ j = 8 ∨ j = 9 → k ≤ vk I.k + 2 →
        wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s1 := slot_lt (w := vk I.k) (show nOne < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nD < 32 by decide)
  have s6 := slot_lt (w := vk I.k) (show nB < 32 by decide)
  have s7 := slot_lt (w := vk I.k) (show nBy < 32 by decide)
  have s10 := slot_lt (w := vk I.k) (show 2 * wB < 32 by decide)
  have e10 : slot (Wk I.k) wB = slot (vk I.k) (2 * wB) := slot_wide _ _
  have bB : slot (Wk I.k) wB + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bS : slot (Wk I.k) wSq + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bB' : slot (2 * vk I.k + 2) wB + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bB
  have bS' : slot (2 * vk I.k + 2) wSq + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bS
  have one' : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [one]; exact Nat.one_lt_two_pow (by omega)), one]
  unfold square
  simp only [seqs]
  refine WP.seq (WP.mono (ones_ok s) fun s₁ ⟨⟨h15, _, m₁⟩, k₁⟩ => ?_)
  have g₁ := h.same m₁ k₁ (by decide)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := nB) (by decide)) fun s₂ ⟨_, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (addA_ok g₂.ws (o := nB) (a := nD) (b := nOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (c := true) ((k₂.gpr .x15 (by decide)).trans h15)) fun s₃ ⟨v₃, _, o₃, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (by omega) o₃ k₃ (by decide)
  simp only [↓reduceIte] at v₃
  rw [o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, hq,
    o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), m₁, one'] at v₃
  -- `y := b`.
  refine WP.seq (WP.mono (zeroA_ok g₃.ws (j := nBy) (by decide)) fun s₄ ⟨z₄, o₄, _, _, _, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok g₄.ws (o := nBy) (a := nB) (by decide) (by decide) (by decide))
    fun s₅ ⟨v₅, o₅, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (by omega) o₅ k₅ (by decide)
  rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₃] at v₅
  -- `x := b` and `a := 0`, wide.
  refine WP.seq (WP.mono (g₅.setWid_ok L) fun s₆ ⟨g₆, f₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₆.ws (j := wB) (by decide)) fun s₇ ⟨z₇, o₇, _, _, _, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (Nat.le_refl _) o₇ k₇ (by decide)
  refine WP.seq (WP.mono (zeroA_ok g₇.ws (j := wSq) (by decide)) fun s₈ ⟨z₈, o₈, _, _, _, k₈⟩ => ?_)
  have g₈ := g₇.out (by decide) (Nat.le_refl _) o₈ k₈ (by decide)
  refine WP.seq (WP.mono (g₈.setNar_ok L) fun s₉ ⟨g₉, f₉, k₉⟩ => ?_)
  refine WP.seq (WP.mono (copyA_ok g₉.ws (o := 2 * wB) (a := nB) (by decide) (by decide) (by decide))
    fun s₁₀ ⟨v₁₀, o₁₀, _, _, k₁₀⟩ => ?_)
  have g₁₀ := g₉.out (by decide) (by omega) o₁₀ k₁₀ (by decide)
  have b₉ : wv s₉.mem I.B (slot (vk I.k) nB) (vk I.k) = (q + 1) % 2 ^ (64 * vk I.k) := by
    rw [Frm.hdrW_wv f₉ (slot_ge _ _) (by omega), o₈.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₇.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₆ (slot_ge _ _) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₃]
  rw [b₉] at v₁₀
  have xb : wv s₁₀.mem I.B (slot (Wk I.k) wB) (Wk I.k) = (q + 1) % 2 ^ (64 * vk I.k) := by
    rw [hW, wide_of_zero (i := wB) (m := s₉.mem) (by
        rw [Frm.hdrW_wv f₉ (slot_ge _ _) (by omega), o₈.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]
        exact z₇) o₁₀ (by omega), v₁₀]
  have zy : word s₁₀.mem I.B (slot (vk I.k) nBy + 8 * vk I.k) = 0 := by
    rw [o₁₀.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_word f₉ (by have := slot_ge (vk I.k) nBy; omega) (by omega),
      o₈.word (wdw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₇.word (wdw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_word f₆ (by have := slot_ge (vk I.k) nBy; omega) (by omega), o₅.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₄ (vk I.k) (by omega)
  have y₁₀ : wv s₁₀.mem I.B (slot (vk I.k) nBy) (vk I.k) = (q + 1) % 2 ^ (64 * vk I.k) := by
    rw [o₁₀.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₉ (slot_ge _ _) (by omega),
      o₈.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      o₇.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₆ (slot_ge _ _) (by omega), v₅]
  have a₁₀ : wv s₁₀.mem I.B (slot (Wk I.k) wSq) (Wk I.k) = 0 := by
    rw [o₁₀.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₉ (slot_ge _ _) (by omega),
      wv_low_of_lt (w := Wk I.k + 2) (by omega) (by rw [z₈]; exact Nat.two_pow_pos _), z₈]
  refine WP.mono (product_ok g₁₀ L pidxS zy) fun t hI => ⟨hI.g, ?_, ?_, fun j k hj hk => ?_⟩
  · have sj := slot_lt (w := vk I.k) (show nB < 32 by decide)
    rw [prod_keep hb32 (by decide) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hI.frm, o₁₀.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), b₉]
  · have := congrArg (fun p => p.2.2) hI.val
    simp only at this
    rw [this, y₁₀, xb, a₁₀]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    have e5 : wB = 5 := rfl
    have e6 : wSq = 6 := rfl
    have e7 : nBy = 7 := rfl
    have e6' : nB = 6 := rfl
    have e9 : wT = 9 := rfl
    rw [prod_keep hb32 (by omega) hk (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hI.frm,
      o₁₀.wv (rd_sep (by omega) hk (by omega)) (by omega), Frm.hdrW_wv f₉ (slot_ge _ _) (by omega),
      o₈.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      o₇.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega), Frm.hdrW_wv f₆ (slot_ge _ _) (by omega),
      o₅.wv (rd_sep (by omega) hk (by omega)) (by omega), o₄.wv (rd_sep (by omega) hk (by omega)) (by omega),
      o₃.wv (rd_sep (by omega) hk (by omega)) (by omega), o₂.wv (rd_sep (by omega) hk (by omega)) (by omega), m₁]

theorem ok4_eq (sq f x : Nat) : (!(decide (sq < f) || decide (x < 1))) = (decide (f ≤ sq) && decide (1 ≤ x)) := by
  by_cases a : f ≤ sq <;> by_cases b : 1 ≤ x <;> simp [a, b] <;> omega

/-- `minus4n`: `X = b² - 4 n` modulo `2^(64 W)` (wide array 7), and `4 n ≤ b²` and `1 ≤ X` and'ed into the mask. -/
theorem minus4n_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {N SQ : Nat}
    (hN : wv s.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N) (hS : wv s.mem I.B (slot (Wk I.k) wSq) (Wk I.k) = SQ) :
    WP isa minus4n s fun t =>
      G I m₀ (Wk I.k) (c && decide (fourN (64 * Wk I.k) N ≤ SQ) &&
        decide (1 ≤ wsub (64 * Wk I.k) SQ (fourN (64 * Wk I.k) N))) t ∧
      wv t.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wsub (64 * Wk I.k) SQ (fourN (64 * Wk I.k) N) ∧
      (∀ j k, j < 8 → k ≤ vk I.k + 2 → wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 := hb32_of h L
  have bN : slot (Wk I.k) wN + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bS : slot (Wk I.k) wSq + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bX : slot (Wk I.k) wX4 + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bO : slot (Wk I.k) wOne + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bT : slot (Wk I.k) wT + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  unfold minus4n
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [oneA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (dbl_ok g₁.ws (a := wN) (by decide) (b := false) (fun t h7 _ => c0_ok t h7))
    fun s₂ ⟨v₂, _, o₂, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (by omega) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (dbl_ok g₂.ws (a := wN) (by decide) (b := false) (fun t h7 _ => c0_ok t h7))
    fun s₃ ⟨v₃, _, o₃, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (by omega) o₃ k₃ (by decide)
  rw [v₂, Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hN] at v₃
  have f4 : wv s₃.mem I.B (slot (Wk I.k) wN) (Wk I.k) = fourN (64 * Wk I.k) N := by
    rw [v₃]; simp [fourN]
  refine WP.seq (WP.mono (subA_ok g₃.ws (o := wX4) (a := wSq) (b := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨v₄, h15₄, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  have sq₃ : wv s₃.mem I.B (slot (Wk I.k) wSq) (Wk I.k) = SQ := by
    rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hS]
  rw [f4, sq₃] at v₄ h15₄
  have hX : wv s₄.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wsub (64 * Wk I.k) SQ (fourN (64 * Wk I.k) N) :=
    sub_wsub (wv_lt _ _ _ _) v₄
  refine WP.mono (andMask_ok g₄ h15₄) fun s₅ ⟨g₅, o₅, k₅⟩ => ?_
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (oneA_ok g₅ (j := wOne) (by decide))
    fun s₆ ⟨g₆, v₆, o₆, k₆⟩ => ?_)
  have hX₆ : wv s₆.mem I.B (slot (Wk I.k) wX4) (Wk I.k) = wsub (64 * Wk I.k) SQ (fourN (64 * Wk I.k) N) := by
    rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), o₅.wv (hd_sep (by decide)) (by omega), hX]
  have one₆ : wv s₆.mem I.B (slot (Wk I.k) wOne) (Wk I.k) = 1 := by
    rw [wv_low_of_lt (w := Wk I.k + 2) (by omega) (by rw [v₆]; exact Nat.one_lt_two_pow (by omega)), v₆]
  simp only [seqs]
  refine WP.seq (WP.mono (subA_ok g₆.ws (o := wT) (a := wX4) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₇ ⟨_, h15₇, _, o₇, k₇⟩ => ?_)
  have g₇ := g₆.out (by decide) (by omega) o₇ k₇ (by decide)
  rw [hX₆, one₆] at h15₇
  refine WP.mono (andMask_ok g₇ h15₇) fun t ⟨gt, ot, _⟩ => ⟨gt, ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (hd_sep (by decide)) (by omega), o₇.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hX₆]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    have e4 : wN = 4 := rfl
    have e7 : wX4 = 7 := rfl
    have e8 : wOne = 8 := rfl
    have e9 : wT = 9 := rfl
    rw [ot.wv (hd_sep (by decide)) (by omega), o₇.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      o₆.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega), o₅.wv (hd_sep (by decide)) (by omega),
      o₄.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      o₃.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      o₂.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega), Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]

end VG.Proof.Rsa.AArch64.Rd
