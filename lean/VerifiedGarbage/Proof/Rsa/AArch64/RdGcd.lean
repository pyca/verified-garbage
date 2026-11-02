module
-- separate module: the GCD's proof, which alone needs `InvLaw`'s inverse, builds beside the products'

public import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: the GCD

`gcd_ok`: `gcd(u, x)` for the odd `u`, by the inverse modulo `u` (`InvLaw`),
or 1 for `u = 1`, into `u`'s array and its copy (narrow array 7).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.Recover (zeroMask)

/-- What the GCD keeps: `n`, one and `X`. -/
theorem gcd_keep {B : Addr} {v : Nat} {m m' : Mem} (hb : slot v 32 ≤ 2 ^ 64)
    (F : Frm B [ar v 2, ar v 3, ar v 4, ar v 5, ar v 6, ar v 7] m m') :
    wv m' B (slot v 0) v = wv m B (slot v 0) v ∧ wv m' B (slot v nOne) (v + 2) = wv m B (slot v nOne) (v + 2) ∧
    wv m' B (slot (2 * v + 2) wX) (2 * v + 2) = wv m B (slot (2 * v + 2) wX) (2 * v + 2) := by
  have s1 := slot_lt (w := v) (show nOne < 32 by decide)
  have s0 := slot_lt (w := v) (show 0 < 32 by decide)
  have s13 := slot_lt (w := v) (show 13 < 32 by decide)
  have e : slot (2 * v + 2) wX = slot v 12 := slot_wide _ _
  have e13 : slot v 13 = slot v 12 + 8 * (v + 2) := slot_succ v 12
  refine ⟨F.wv_eq ?_ (by omega), F.wv_eq ?_ (by omega), F.wv_eq ?_ (by omega)⟩ <;>
  · simp only [ar, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact rd_sep (by decide) (by omega) (by omega)
      | exact wn_sep (by decide) (by decide) (by omega) (by omega)

theorem gcd_one_or {U X g : Nat} (h : U = 1 ∨ g = Nat.gcd X U) :
    (if decide (U = 1) then 1 else g) = Nat.gcd U X := by
  by_cases e : U = 1
  · simp [e]
  · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]; rw [h.resolve_left e, Nat.gcd_comm]

/-- `gcd`: `gcd(u, x)` into narrow arrays 2 and 7, for an odd `u`. -/
theorem gcd_ok [InvLaw] {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I)
    {U X : Nat} (hU : wv s.mem I.B (slot (vk I.k) nU) (vk I.k) = U) (hodd : U % 2 = 1)
    (hX : wv s.mem I.B (slot (vk I.k) nXn) (vk I.k) = X)
    (hz : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0)
    (one : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1) :
    WP isa gcd s fun t => G I m₀ (vk I.k) c t ∧ wv t.mem I.B (slot (vk I.k) gT) (vk I.k) = Nat.gcd U X ∧
      word t.mem I.B (slot (vk I.k) gT + 8 * vk I.k) = 0 ∧
      Frm I.B [ar (vk I.k) 2, ar (vk I.k) 3, ar (vk I.k) 4, ar (vk I.k) 5, ar (vk I.k) 6, ar (vk I.k) 7] s.mem t.mem := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  have s1 := slot_lt (w := vk I.k) (show nOne < 32 by decide)
  have s2 := slot_lt (w := vk I.k) (show nU < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nXn < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show gM < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show gX₁ < 32 by decide)
  have s6 := slot_lt (w := vk I.k) (show gX₂ < 32 by decide)
  have s7 := slot_lt (w := vk I.k) (show gT < 32 by decide)
  have one' : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [one]; exact Nat.one_lt_two_pow (by omega)), one]
  have e : gcd = seqs ([zeroA gM, copyA gM nU] ++ (oneA gX₁ ++ ([zeroA gX₂, inverse nXn nU gX₁ gX₂ gM gT] ++
      (eqA gM nOne ++ [.block zeroMask, selA nU nOne, zeroA gT, copyA gT nU])))) := by
    simp only [gcd, List.append_assoc]
  rw [e]
  -- `m := u`.
  refine wp_seqs_append (by simp) (by simp [oneA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := gM) (by decide)) fun s₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have g₁ := h.out (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (copyA_ok g₁.ws (o := gM) (a := nU) (by decide) (by decide) (by decide))
    fun s₂ ⟨v₂, o₂, _, _, k₂⟩ => ?_
  have g₂ := g₁.out (by decide) (by omega) o₂ k₂ (by decide)
  rw [o₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hU] at v₂
  -- `x₁ := 1`, `x₂ := 0`.
  refine wp_seqs_append (by simp [oneA]) (by simp) (WP.mono (oneA_ok g₂ (j := gX₁) (by decide))
    fun s₃ ⟨g₃, v₃, o₃, k₃⟩ => ?_)
  refine wp_seqs_append (by simp) (by simp [eqA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok g₃.ws (j := gX₂) (by decide)) fun s₄ ⟨z₄, o₄, _, _, _, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  -- The inverse's inputs.
  have uM : wv s₄.mem I.B (slot (vk I.k) gM) (vk I.k) = U := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₂]
  have uU : wv s₄.mem I.B (slot (vk I.k) nU) (vk I.k) = U := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hU]
  have xX : wv s₄.mem I.B (slot (vk I.k) nXn) (vk I.k) = X := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), hX]
  have zX : word s₄.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0 := by
    rw [o₄.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁.word (wd_sep (by decide) (by omega) (by omega)) (by omega), hz]
  have x1 : wv s₄.mem I.B (slot (vk I.k) gX₁) (vk I.k) = 1 := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [v₃]; exact Nat.one_lt_two_pow (by omega)), v₃]
  have x2 : wv s₄.mem I.B (slot (vk I.k) gX₂) (vk I.k) = 0 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₄]; exact Nat.two_pow_pos _), z₄]
  have one₄ : wv s₄.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), one']
  refine (WP.mono (InvLaw.inverse_ok g₄.ws (iU := nXn) (iV := nU) (iX₁ := gX₁) (iX₂ := gX₂) (iM := gM) (iT := gT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) zX (by rw [uU, uM]) x1 x2) fun s₅ ⟨_, f₅, k₅, hinv⟩ => ?_)
  have g₅ := g₄.step f₅ (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact slot_ge _ _)
    (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Nat.le_trans (slot_lt (by decide)) g₄.ws.hZ) k₅ (by decide)
  have f5 : ∀ {j k : Nat}, j ≠ nXn → j ≠ nU → j ≠ gX₁ → j ≠ gX₂ → j ≠ gT → j < 32 → k ≤ vk I.k + 2 →
      wv s₅.mem I.B (slot (vk I.k) j) k = wv s₄.mem I.B (slot (vk I.k) j) k := fun a b c' d e hj hk =>
    f₅.wv_eq (by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      · exact rd_sep a hk (Nat.le_refl _)
      · exact rd_sep b hk (Nat.le_refl _)
      · exact rd_sep c' hk (Nat.le_refl _)
      · exact rd_sep d hk (Nat.le_refl _)
      · exact rd_sep e hk (Nat.le_refl _)) (by have := slot_lt (w := vk I.k) hj; omega)
  have uM₅ : wv s₅.mem I.B (slot (vk I.k) gM) (vk I.k) = U := by
    rw [f5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), uM]
  have one₅ : wv s₅.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [f5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), one₄]
  have hg : U = 1 ∨ wv s₅.mem I.B (slot (vk I.k) nU) (vk I.k) = Nat.gcd X U := by
    by_cases e1 : U = 1
    · exact .inl e1
    · right; rw [uM, xX] at hinv; exact (hinv hodd (by omega)).1
  -- `u = 1`.
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok g₅.ws (a := gM) (b := nOne) (by decide) (by decide))
    fun s₆ ⟨h9, m₆, _, _, k₆⟩ => ?_)
  rw [uM₅, one₅] at h9
  have g₆ := g₅.same m₆ k₆ (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroMask_ok s₆) fun s₇ ⟨⟨h15, _, m₇⟩, k₇⟩ => ?_)
  have g₇ := g₆.same m₇ k₇ (by decide)
  have e15 : decide (s₆.gpr .x9 = 0) = decide (U = 1) := decide_eq_decide.mpr h9
  rw [e15] at h15
  refine WP.seq (WP.mono (selA_ok g₇.ws (o := nU) (a := nOne) (by decide) (by decide) (by decide) h15)
    fun s₈ ⟨v₈, o₈, k₈⟩ => ?_)
  have g₈ := g₇.out (by decide) (by omega) o₈ k₈ (by decide)
  rw [m₇, m₆, one₅, gcd_one_or hg] at v₈
  refine WP.seq (WP.mono (zeroA_ok g₈.ws (j := gT) (by decide)) fun s₉ ⟨z₉, o₉, _, _, _, k₉⟩ => ?_)
  have g₉ := g₈.out (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.mono (copyA_ok g₉.ws (o := gT) (a := nU) (by decide) (by decide) (by decide))
    fun t ⟨v₁₀, o₁₀, _, _, k₁₀⟩ => ⟨g₉.out (by decide) (by omega) o₁₀ k₁₀ (by decide), ?_, ?_, ?_⟩
  · rw [v₁₀, o₉.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₈]
  · rw [o₁₀.word (.inr (by omega)) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₉ (vk I.k) (by omega)
  · intro x hx
    have a2 := hx (ar (vk I.k) nU) (.head _)
    have a4 := hx (ar (vk I.k) gM) (.tail _ (.tail _ (.head _)))
    have a5 := hx (ar (vk I.k) gX₁) (.tail _ (.tail _ (.tail _ (.head _))))
    have a6 := hx (ar (vk I.k) gX₂) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    have a7 := hx (ar (vk I.k) gT) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    simp only at a2 a4 a5 a6 a7
    rw [o₁₀ x (a7.imp id fun h => by omega), o₉ x a7, o₈ x (a2.imp id fun h => by omega), m₇, m₆,
      f₅ x (fun r hr => hx r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact .tail _ (.head _)
        · exact .head _
        · exact .tail _ (.tail _ (.tail _ (.head _)))
        · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
        · exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      o₄ x a6, o₃ x a5, o₂ x (a4.imp id fun h => by omega), o₁ x a4]



end VG.Proof.Rsa.AArch64.Rd
