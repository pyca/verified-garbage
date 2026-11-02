module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdProd
import VerifiedGarbage.Proof.Rsa.AArch64.RdTwos
import VerifiedGarbage.Proof.Rsa.AArch64.CvLoad
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: `a` and the divisions

`aProd_ok`: `a`, the product of the GCD and `2^k X` (wide array 7);
`divA_ok`: `m = a / n` and `r = a mod n` (wide arrays 7 and 6), and `m < n`
and'ed into the mask; `divB_ok`: the quotient and remainder of `n - r` by
`m + 1` (narrow), and the remainder zero and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.RecoverDet

/-- A narrow array apart from a product's is kept by it. -/
theorem prod_keep {B : Addr} {v y x a t j k : Nat} {m m' : Mem} (hb : slot v 32 ≤ 2 ^ 64) (hj : j < 32)
    (hk : k ≤ v + 2) (hjy : j ≠ y) (hx1 : j ≠ 2 * x) (hx2 : j ≠ 2 * x + 1) (ha1 : j ≠ 2 * a) (ha2 : j ≠ 2 * a + 1)
    (ht1 : j ≠ 2 * t) (ht2 : j ≠ 2 * t + 1) (F : Frm B (prodRanges v y x a t) m m') :
    wv m' B (slot v j) k = wv m B (slot v j) k := by
  have := slot_lt (w := v) hj
  refine Frm.hdr_wv F (slot_ge _ _) (by omega) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact rd_sep hjy hk (by omega)
  · exact nw_sep ht1 ht2 hk (by omega)
  · exact nw_sep ha1 ha2 hk (by omega)
  · exact nw_sep hx1 hx2 hk (by omega)

theorem hb32_of {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) :
    slot (vk I.k) 32 ≤ 2 ^ 64 := by
  have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
  have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega

theorem pidxA : PIdx gT wX wA wT := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `aProd`: `a = (prodStep^[64 v] (g, X, 0)).2.2` into wide array 7. -/
theorem aProd_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I)
    (hz : word s.mem I.B (slot (vk I.k) gT + 8 * vk I.k) = 0) :
    WP isa aProd s fun t => G I m₀ (vk I.k) c t ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = ((prodStep (64 * Wk I.k))^[64 * vk I.k]
        (wv s.mem I.B (slot (vk I.k) gT) (vk I.k), wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k), 0)).2.2 ∧
      (∀ j k, j < 12 → j ≠ gT → k ≤ vk I.k + 2 → wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s7 := slot_lt (w := vk I.k) (show gT < 32 by decide)
  have bA : slot (Wk I.k) wA + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bX : slot (Wk I.k) wX + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bA' : slot (2 * vk I.k + 2) wA + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bA
  unfold aProd
  simp only [seqs]
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := wA) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (g₂.setNar_ok L) fun s₃ ⟨g₃, f₃, k₃⟩ => ?_)
  have hY : wv s₃.mem I.B (slot (vk I.k) gT) (vk I.k) = wv s.mem I.B (slot (vk I.k) gT) (vk I.k) := by
    rw [Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]
  have hX : wv s₃.mem I.B (slot (Wk I.k) wX) (Wk I.k) = wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k) := by
    rw [Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]
  have hA : wv s₃.mem I.B (slot (Wk I.k) wA) (Wk I.k) = 0 := by
    rw [Frm.hdrW_wv f₃ (slot_ge _ _) (by omega),
      wv_low_of_lt (w := Wk I.k + 2) (by omega) (by rw [z₂]; exact Nat.two_pow_pos _), z₂]
  have hz₃ : word s₃.mem I.B (slot (vk I.k) gT + 8 * vk I.k) = 0 := by
    rw [Frm.hdrW_word f₃ (by have := slot_ge (vk I.k) gT; omega) (by omega),
      o₂.word (wdw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_word f₁ (by have := slot_ge (vk I.k) gT; omega) (by omega), hz]
  refine WP.mono (product_ok g₃ L pidxA hz₃) fun t hI => ⟨hI.g, ?_, fun j k hj hjy hk => ?_⟩
  · have := congrArg (fun p => p.2.2) hI.val
    simp only at this
    rw [this, hY, hX, hA]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    rw [prod_keep hb32 (by omega) hk hjy (by unfold wX; omega) (by unfold wX; omega) (by unfold wA; omega)
      (by unfold wA; omega) (by unfold wT; omega) (by unfold wT; omega) hI.frm,
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega),
      o₂.wv (nw_sep (by unfold wA; omega) (by unfold wA; omega) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]

/-- A wide array whose words above the narrow width are zero has the narrow value. -/
theorem wide_low {m : Mem} {B : Addr} {v d : Nat} (hz : wv m B (d + 8 * v) (v + 2) = 0) :
    wv m B d (2 * v + 2) = wv m B d v := by
  rw [show 2 * v + 2 = v + (v + 2) by omega, wv_add, hz, Nat.mul_zero, Nat.add_zero]

/-- `divA`: `m` and `r`, `n` wide (wide array 4), and `m < n` and'ed into the mask. -/
theorem divA_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I) {A N : Nat}
    (hA : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A) (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (hN0 : 0 < N) :
    WP isa divA s fun t => G I m₀ (Wk I.k) (c && decide (A / N < N)) t ∧
      wv t.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A / N ∧
      wv t.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = A % N ∧
      wv t.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N ∧
      (∀ j k, j < 8 → k ≤ vk I.k + 2 → wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hv2 : vk I.k ≤ 200 := by have := L.k2; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s0 := slot_lt (w := vk I.k) (show 0 < 32 by decide)
  have s8 := slot_lt (w := vk I.k) (show nN < 32 by decide)
  have e48 : slot (Wk I.k) wN = slot (vk I.k) nN := slot_wide _ _
  have bN : slot (Wk I.k) wN + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bA : slot (Wk I.k) wA + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bX : slot (Wk I.k) wX + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bT : slot (Wk I.k) wT + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := h.bndW L (by decide) (Nat.le_refl _)
  have bA' : slot (2 * vk I.k + 2) wA + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bA
  have bN' : slot (2 * vk I.k + 2) wN + 8 * (Wk I.k + 2) ≤ 2 ^ 64 := bN
  unfold divA
  simp only [seqs]
  -- `n` wide.
  refine WP.seq (WP.mono (h.setWid_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroA_ok g₁.ws (j := wN) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have g₂ := g₁.out (by decide) (Nat.le_refl _) o₂ k₂ (by decide)
  refine WP.seq (WP.mono (g₂.setNar_ok L) fun s₃ ⟨g₃, f₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (copyA_ok g₃.ws (o := nN) (a := Public.aN) (by decide) (by decide) (by decide))
    fun s₄ ⟨v₄, o₄, _, _, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  refine WP.seq (WP.mono (g₄.setWid_ok L) fun s₅ ⟨g₅, f₅, k₅⟩ => ?_)
  have hz₂ : wv s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2) = 0 := by
    have := wv_add s₂.mem I.B (slot (Wk I.k) wN) (vk I.k) (vk I.k + 2 + 2)
    rw [show vk I.k + (vk I.k + 2 + 2) = Wk I.k + 2 by omega, z₂, e48] at this
    have e := wv_add s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2) 2
    have : 2 ^ (64 * vk I.k) * wv s₂.mem I.B (slot (vk I.k) nN + 8 * vk I.k) (vk I.k + 2 + 2) = 0 := by omega
    have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    rw [e] at this; omega
  have nW₅ : wv s₅.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N := by
    rw [Frm.hdrW_wv f₅ (slot_ge _ _) (by omega), e48, hW, wide_low, v₄,
      show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl,
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (nw_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hN]
    rw [o₄.wv (.inr (by omega)) (by omega), Frm.hdrW_wv f₃ (by have := slot_ge (vk I.k) nN; omega) (by omega), hz₂]
  have aW₅ : wv s₅.mem I.B (slot (Wk I.k) wA) (Wk I.k) = A := by
    rw [Frm.hdrW_wv f₅ (slot_ge _ _) (by omega), o₄.wv (wn_sep (by decide) (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega), o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hA]
  -- The division.
  refine WP.seq (WP.mono (divmod_ok g₅.ws (iQ := wA) (iR := wX) (iD := wN) (iT := wT) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨_, f₆, k₆, hdiv⟩ => ?_)
  rw [nW₅, aW₅] at hdiv
  obtain ⟨hr₆, hq₆⟩ := hdiv hN0
  have g₆ := g₅.step f₆ (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slot_ge _ _)
    (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Nat.le_trans (slot_lt (by decide)) g₅.ws.hZ) k₆ (by decide)
  have nW₆ : wv s₆.mem I.B (slot (Wk I.k) wN) (Wk I.k) = N := by
    rw [f₆.wv_eq (by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> exact rd_sep (by decide) (by omega) (Nat.le_refl _)) (by omega), nW₅]
  -- `m < n`.
  refine WP.seq (WP.mono (cmpSet_ok' g₆.ws wA wN) fun s₇ ⟨⟨h16, h17, h14, _, _, h7, hc, m₇⟩, k₇⟩ => ?_)
  have sA := g₆.ws.sl (j := wA) (by decide)
  have sN := g₆.ws.sl (j := wN) (by decide)
  refine WP.seq (WP.mono (cmpLoop_ok (g₆.ws.scr.congr k₇.wr) h16 h17 h14 hc (by omega) (by omega) (by omega)
    (by omega)) fun s₈ ⟨c₈, m₈, k₈⟩ => ?_)
  rw [m₇, hq₆, nW₆] at c₈
  have g₈ := (g₆.same m₇ k₇ (by decide)).same m₈ k₈ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrowMask_ok s₈ ((k₈.gpr .x7 (by decide)).trans h7)) fun s₉ ⟨⟨h15, m₉, _⟩, k₉⟩ => ?_
  rw [c₈, Bool.not_not] at h15
  refine WP.mono (andMask_ok (g₈.same m₉ k₉ (by decide)) h15) fun t ⟨gt, ot, _⟩ => ⟨gt, ?_, ?_, ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (hd_sep (by decide)) (by omega), m₉, m₈, m₇, hq₆]
  · rw [ot.wv (hd_sep (by decide)) (by omega), m₉, m₈, m₇, hr₆]
  · rw [ot.wv (hd_sep (by decide)) (by omega), m₉, m₈, m₇, nW₆]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    have eA : wA = 7 := rfl
    have eX : wX = 6 := rfl
    have eT : wT = 9 := rfl
    have eN : wN = 4 := rfl
    have enN : nN = 8 := rfl
    rw [ot.wv (hd_sep (by decide)) (by omega), m₉, m₈, m₇,
      f₆.wv_eq (by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl) <;>
          exact nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      Frm.hdrW_wv f₅ (slot_ge _ _) (by omega), o₄.wv (rd_sep (by omega) hk (by omega)) (by omega),
      Frm.hdrW_wv f₃ (slot_ge _ _) (by omega),
      o₂.wv (nw_sep (by omega) (by omega) hk (by omega)) (by omega),
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]

/-- `divB`: `m + 1` and `n - r`, their quotient `q` (narrow array 3) and remainder (4), and the
remainder zero and'ed into the mask. -/
theorem divB_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (Wk I.k) c s) (L : RpLens I) {M R N : Nat}
    (hM : wv s.mem I.B (slot (Wk I.k) wA) (Wk I.k) = M) (hR : wv s.mem I.B (slot (Wk I.k) wX) (Wk I.k + 1) = R)
    (hN : wv s.mem I.B (slot (vk I.k) 0) (vk I.k) = N)
    (one : wv s.mem I.B (slot (vk I.k) nOne) (vk I.k + 2) = 1) :
    WP isa divB s fun t => ∃ q rem : Nat,
      G I m₀ (vk I.k) (decide (rem = 0) && c) t ∧ wv t.mem I.B (slot (vk I.k) nD) (vk I.k) = q ∧
      (0 < (M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k) →
        q = wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) / ((M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k)) ∧
        rem = wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) % ((M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k))) ∧
      (∀ j k, (j < 2 ∨ (6 ≤ j ∧ j < 12)) → k ≤ vk I.k + 2 →
        wv t.mem I.B (slot (vk I.k) j) k = wv s.mem I.B (slot (vk I.k) j) k) := by
  have hW : Wk I.k = 2 * vk I.k + 2 := rfl
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hv2 : vk I.k ≤ 200 := by have := L.k2; simp only [vk]; omega
  have hb32 := hb32_of h L
  have s0 := slot_lt (w := vk I.k) (show 0 < 32 by decide)
  have s1 := slot_lt (w := vk I.k) (show nOne < 32 by decide)
  have s14 := slot_lt (w := vk I.k) (show 2 * wA < 32 by decide)
  have s12 := slot_lt (w := vk I.k) (show 2 * wX < 32 by decide)
  have e14 : slot (Wk I.k) wA = slot (vk I.k) (2 * wA) := slot_wide _ _
  have e12 : slot (Wk I.k) wX = slot (vk I.k) (2 * wX) := slot_wide _ _
  have s2 := slot_lt (w := vk I.k) (show nM1 < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nD < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show nRem < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show nZ < 32 by decide)
  have s5' := slot_lt (w := vk I.k) (show nDt < 32 by decide)
  unfold divB
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) ?_
  simp only [seqs]
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (h.setNar_ok L) fun s₁ ⟨g₁, f₁, k₁⟩ => ?_
  refine WP.mono (ones_ok s₁) fun s₂ ⟨⟨h15, _, m₂⟩, k₂⟩ => ?_
  have g₂ := g₁.same m₂ k₂ (by decide)
  have mlow : wv s₂.mem I.B (slot (vk I.k) (2 * wA)) (vk I.k) = M % 2 ^ (64 * vk I.k) := by
    rw [m₂, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k by omega), ← e14, Frm.hdrW_wv f₁ (slot_ge _ _) (by
      have := h.bndW L (j := wA) (k := Wk I.k) (by decide) (by omega); omega), hM]
  have rlow : wv s₂.mem I.B (slot (vk I.k) (2 * wX)) (vk I.k) = R % 2 ^ (64 * vk I.k) := by
    rw [m₂, ← wv_mod _ _ _ (show vk I.k ≤ Wk I.k + 1 by omega), ← e12, Frm.hdrW_wv f₁ (slot_ge _ _) (by
      have := h.bndW L (j := wX) (k := Wk I.k + 1) (by decide) (by omega); omega), hR]
  have n₂ : wv s₂.mem I.B (slot (vk I.k) 0) (vk I.k) = N := by
    rw [m₂, Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), hN]
  have one₂ : wv s₂.mem I.B (slot (vk I.k) nOne) (vk I.k) = 1 := by
    rw [m₂, Frm.hdrW_wv f₁ (slot_ge _ _) (by omega), wv_low_of_lt (w := vk I.k + 2) (by omega)
      (by rw [one]; exact Nat.one_lt_two_pow (by omega)), one]
  -- `m + 1`.
  refine WP.seq (WP.mono (zeroA_ok g₂.ws (j := nM1) (by decide)) fun s₃ ⟨_, o₃, _, _, _, k₃⟩ => ?_)
  have g₃ := g₂.out (by decide) (Nat.le_refl _) o₃ k₃ (by decide)
  refine WP.seq (WP.mono (addA_ok g₃.ws (o := nM1) (a := 2 * wA) (b := nOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (c := true) ((k₃.gpr .x15 (by decide)).trans h15)) fun s₄ ⟨v₄, _, o₄, k₄⟩ => ?_)
  have g₄ := g₃.out (by decide) (by omega) o₄ k₄ (by decide)
  simp only [↓reduceIte] at v₄
  rw [o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), mlow,
    o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), one₂] at v₄
  -- `n - r`.
  refine WP.seq (WP.mono (zeroA_ok g₄.ws (j := nD) (by decide)) fun s₅ ⟨_, o₅, _, _, _, k₅⟩ => ?_)
  have g₅ := g₄.out (by decide) (Nat.le_refl _) o₅ k₅ (by decide)
  refine WP.seq (WP.mono (subA_ok g₅.ws (o := nD) (a := Public.aN) (b := 2 * wX) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨v₆, _, _, o₆, k₆⟩ => ?_)
  have g₆ := g₅.out (by decide) (by omega) o₆ k₆ (by decide)
  have rlow₅ : wv s₅.mem I.B (slot (vk I.k) (2 * wX)) (vk I.k) = R % 2 ^ (64 * vk I.k) := by
    rw [o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), rlow]
  have n₅ : wv s₅.mem I.B (slot (vk I.k) Public.aN) (vk I.k) = N := by
    rw [show slot (vk I.k) Public.aN = slot (vk I.k) 0 from rfl, o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), n₂]
  rw [rlow₅, n₅] at v₆
  have hd : wv s₆.mem I.B (slot (vk I.k) nD) (vk I.k) = wsub (64 * vk I.k) N (R % 2 ^ (64 * vk I.k)) :=
    sub_wsub (wv_lt _ _ _ _) v₆
  have hm1 : wv s₆.mem I.B (slot (vk I.k) nM1) (vk I.k) = (M % 2 ^ (64 * vk I.k) + 1) % 2 ^ (64 * vk I.k) := by
    rw [o₆.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₅.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₄]
  -- The division.
  refine WP.seq (WP.mono (divmod_ok g₆.ws (iQ := nD) (iR := nRem) (iD := nM1) (iT := nDt) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₇ ⟨_, f₇, k₇, hdiv⟩ => ?_)
  rw [hd, hm1] at hdiv
  have g₇ := g₆.step f₇ (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slot_ge _ _)
    (fun r hr => by
      simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Nat.le_trans (slot_lt (by decide)) g₆.ws.hZ) k₇ (by decide)
  refine WP.mono (zeroA_ok g₇.ws (j := nZ) (by decide)) fun s₈ ⟨z₈, o₈, _, _, _, k₈⟩ => ?_
  have g₈ := g₇.out (by decide) (Nat.le_refl _) o₈ k₈ (by decide)
  have q₈ : wv s₈.mem I.B (slot (vk I.k) nD) (vk I.k) = wv s₇.mem I.B (slot (vk I.k) nD) (vk I.k) :=
    o₈.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)
  have r₈ : wv s₈.mem I.B (slot (vk I.k) nRem) (vk I.k + 1) = wv s₇.mem I.B (slot (vk I.k) nRem) (vk I.k + 1) :=
    o₈.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)
  have z₈' : wv s₈.mem I.B (slot (vk I.k) nZ) (vk I.k) = 0 := by
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₈]; exact Nat.two_pow_pos _), z₈]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok g₈.ws (a := nRem) (b := nZ) (by decide) (by decide))
    fun s₉ ⟨h9, m₉, _, _, k₉⟩ => ?_)
  rw [z₈'] at h9
  have g₉ := g₈.same m₉ k₉ (by decide)
  refine WP.mono (andZero_ok g₉.ws g₉.msk h9) fun t ⟨⟨mt, _⟩, kt⟩ => ?_
  have ot : Outside I.B (8 * Public.sMask) 8 s₉.mem t.mem := by
    rw [mt]; exact writeW_outside s₉.mem I.B _ (by simp only [Public.sMask, sFn]; omega)
  refine ⟨wv s₇.mem I.B (slot (vk I.k) nD) (vk I.k), wv s₈.mem I.B (slot (vk I.k) nRem) (vk I.k),
    g₉.store mt kt (by decide), ?_, fun hpos => ?_, fun j k hj hk => ?_⟩
  · rw [ot.wv (hd_sep (by decide)) (by omega), m₉, q₈]
  · obtain ⟨hr, hq⟩ := hdiv hpos
    refine ⟨hq, ?_⟩
    rw [wv_low_of_lt (w := vk I.k + 1) (by omega) (by
      rw [r₈, hr]
      exact Nat.lt_trans (Nat.mod_lt _ hpos) (Nat.mod_lt _ (Nat.two_pow_pos _))), r₈, hr]
  · have sj := slot_lt (w := vk I.k) (show j < 32 by omega)
    have e2 : nM1 = 2 := rfl
    have e3 : nD = 3 := rfl
    have e4 : nRem = 4 := rfl
    have e5 : nZ = 5 := rfl
    have e5' : nDt = 5 := rfl
    rw [ot.wv (hd_sep (by decide)) (by omega), m₉, o₈.wv (rd_sep (by omega) hk (by omega)) (by omega),
      f₇.wv_eq (by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl) <;> exact rd_sep (by omega) hk (Nat.le_refl _)) (by omega),
      o₆.wv (rd_sep (by omega) hk (by omega)) (by omega), o₅.wv (rd_sep (by omega) hk (by omega)) (by omega),
      o₄.wv (rd_sep (by omega) hk (by omega)) (by omega), o₃.wv (rd_sep (by omega) hk (by omega)) (by omega), m₂,
      Frm.hdrW_wv f₁ (slot_ge _ _) (by omega)]

end VG.Proof.Rsa.AArch64.Rd
