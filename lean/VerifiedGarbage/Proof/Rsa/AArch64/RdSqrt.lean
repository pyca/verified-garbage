module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.AArch64.RdDiv
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows
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

/-- `square`: `b = q + 1` (narrow array 6) and `b² = (prodStep^[64 v] (b, b, 0)).2.2` (wide array 6), by
rows. -/
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
  have hk1 := L.k1
  have hk2 := L.k2
  have hv1 : 2 ≤ vk I.k := by simp only [vk]; omega
  have hvl : vk I.k < 200 := by simp only [vk]; omega
  have hb32 := hb32_of h L
  have q32 : slot (vk I.k) 32 = 256 + 32 * (8 * (vk I.k + 2)) := rfl
  have q1 : slot (vk I.k) nOne = 256 + 1 * (8 * (vk I.k + 2)) := rfl
  have q3 : slot (vk I.k) nD = 256 + 3 * (8 * (vk I.k + 2)) := rfl
  have q6 : slot (vk I.k) nB = 256 + 6 * (8 * (vk I.k + 2)) := rfl
  have q12 : slot (vk I.k) 12 = 256 + 12 * (8 * (vk I.k + 2)) := rfl
  have q13 : slot (vk I.k) 13 = 256 + 13 * (8 * (vk I.k + 2)) := rfl
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
  -- `b²` by rows into wide array 6.
  refine WP.seq (WP.mono (g₃.setWid_ok L) fun s₄ ⟨g₄, f₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₄.ws (j := wSq) (by decide)) fun s₅ ⟨z₅, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ws_ok g₅.ws.scr g₅.ws.x0 g₅.ws.h256 g₅.ws.hw g₅.ws.hS) fun s₆ ⟨⟨_, h11₆, m₆, _⟩, k₆⟩ => ?_
  refine WP.mono (base_ok wSq .x8 ((k₆.gpr .x0 (by decide)).trans g₅.ws.x0) h11₆) fun s₇ ⟨⟨h8₇, m₇, _⟩, k₇⟩ => ?_
  have g₇ := g₅.same (by rw [m₇, m₆]) (k₆.trans k₇) (by decide)
  refine WP.mono (g₇.setNar_ok L) fun s₈ ⟨g₈, f₈, k₈⟩ => ?_
  refine WP.mono (ws_ok g₈.ws.scr g₈.ws.x0 g₈.ws.h256 g₈.ws.hw g₈.ws.hS) fun s₉ ⟨⟨h12₉, h11₉, m₉, _⟩, k₉⟩ => ?_
  refine WP.mono (base_ok nB .x9 ((k₉.gpr .x0 (by decide)).trans g₈.ws.x0) h11₉) fun s₁₀ ⟨⟨h9₁₀, m₁₀, _⟩, k₁₀⟩ => ?_
  have h12₁₀ : s₁₀.gpr .x12 = BitVec.ofNat 64 (vk I.k) := (k₁₀.gpr .x12 (by decide)).trans h12₉
  refine WP.mono (WP.keep [.x7, .x11, .x13] (Q := fun t => t.gpr .x11 = off I.B (slot (vk I.k) nB) ∧
      t.gpr .x13 = BitVec.ofNat 64 (vk I.k) ∧ t.gpr .x7 = 0 ∧ t.mem = s₁₀.mem) (by brun [h9₁₀, h12₁₀])
    (by decide) (by decide) (by decide +kernel)) fun s₁₁ ⟨⟨h11, h13, h7, m₁₁⟩, k₁₁⟩ => ?_
  have g₁₁ : G I m₀ (vk I.k) c s₁₁ := g₈.same (by rw [m₁₁, m₁₀, m₉]) ((k₉.trans k₁₀).trans k₁₁) (by decide)
  have hn := g₁₁.ws.scr.nowrap
  have z13 := g₁₁.ws.sl (j := 13) (by decide)
  have e12 : slot (Wk I.k) wSq = slot (vk I.k) 12 := slot_wide _ _
  have eW : Wk I.k = vk I.k + vk I.k + 2 := by omega
  -- What the rows read: `b`, and the accumulator zero.
  have mS : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → (d + 8 * n ≤ slot (vk I.k) 12 ∨ slot (vk I.k) 12 + 8 * (Wk I.k + 2) ≤ d) →
      wv s₁₁.mem I.B d n = wv s₃.mem I.B d n := fun d n hd hd' hsep => by
    rw [m₁₁, m₁₀, m₉, Frm.hdrW_wv f₈ hd hd', m₇, m₆, o₅.wv (by rw [e12]; exact hsep) hd', Frm.hdrW_wv f₄ hd hd']
  have hb : wv s₁₁.mem I.B (slot (vk I.k) nB) (vk I.k) = (q + 1) % 2 ^ (64 * vk I.k) := by
    rw [mS _ _ (slot_ge _ _) (by omega) (.inl (by simp only [slot, hdrBytes, nB]; omega)), v₃]
  have hA0 : wv s₁₁.mem I.B (slot (Wk I.k) wSq) (vk I.k + vk I.k + 2) = 0 := by
    rw [← eW, m₁₁, m₁₀, m₉, Frm.hdrW_wv f₈ (slot_ge _ _) (by rw [e12]; omega), m₇, m₆,
      wv_low_of_lt (w := Wk I.k + 2) (by omega) (by rw [z₅]; exact Nat.two_pow_pos _), z₅]
  refine WP.mono (mulRows_ok (ea := slot (vk I.k) nB) (eb := slot (vk I.k) nB) (eA := slot (Wk I.k) wSq)
    (wa := vk I.k) (wb := vk I.k) g₁₁.ws.scr h11 (by rw [k₁₁.gpr .x9 (by decide), h9₁₀]) h13
    (by rw [k₁₁.gpr .x12 (by decide), h12₁₀])
    (by rw [k₁₁.gpr .x8 (by decide), k₁₀.gpr .x8 (by decide), k₉.gpr .x8 (by decide), k₈.gpr .x8 (by decide), h8₇])
    h7 (by omega) (by omega) (by omega) (by rw [e12]; simp only [slot, hdrBytes] at z13 ⊢; omega) (by omega) (by omega)
    (.inl (by rw [e12]; simp only [slot, hdrBytes, nB]; omega)) (.inl (by rw [e12]; simp only [slot, hdrBytes, nB]; omega))
    (by rw [hA0]; exact Nat.two_pow_pos _)) fun t ⟨vt, ot, kt⟩ => ?_
  rw [hA0, Nat.zero_add, hb, ← eW] at vt
  refine ⟨g₁₁.out2 (j := 12) (n := 16 * (vk I.k + 2)) (by decide) (by omega)
    (by rw [← e12]; exact ot.mono (Nat.le_refl _) (by omega)) kt
    (by decide), ?_, ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (.inl (by rw [e12]; simp only [slot, hdrBytes, nB]; omega)) (by omega), hb]
  · have hbl : (q + 1) % 2 ^ (64 * vk I.k) < 2 ^ (64 * Wk I.k) :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
    have hbb : (q + 1) % 2 ^ (64 * vk I.k) * ((q + 1) % 2 ^ (64 * vk I.k)) < 2 ^ (64 * Wk I.k) :=
      calc (q + 1) % 2 ^ (64 * vk I.k) * ((q + 1) % 2 ^ (64 * vk I.k)) < 2 ^ (64 * vk I.k) * 2 ^ (64 * vk I.k) :=
            Nat.mul_lt_mul'' (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
        _ ≤ 2 ^ (64 * Wk I.k) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [vt, prod_iter _ _ _ hbl, Nat.mod_mod, Nat.mod_eq_of_lt hbb]
  · have sB : slot (vk I.k) j + 8 * k ≤ slot (vk I.k) nB ∨ slot (vk I.k) nB + 8 * (vk I.k + 2) ≤ slot (vk I.k) j := by
      rcases hj with hj | rfl | rfl
      · left; have := slot_lt (w := vk I.k) (show j < nB from hj); omega
      all_goals right; simp only [slot, hdrBytes] at q6 ⊢; omega
    have sS : slot (vk I.k) j + 8 * k ≤ slot (vk I.k) 12 := by
      rcases hj with hj | rfl | rfl
      · have := slot_lt (w := vk I.k) (show j < nB from hj); omega
      all_goals simp only [slot, hdrBytes] at q12 ⊢; omega
    have bj : slot (vk I.k) j + 8 * k ≤ 2 ^ 64 := by omega
    rw [ot.wv (.inl (by rw [e12]; exact sS)) bj, mS _ _ (slot_ge _ _) bj (.inl sS),
      o₃.wv (by rcases sB with h | h; exact .inl h; exact .inr (by omega)) bj, o₂.wv sB bj, m₁]

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
