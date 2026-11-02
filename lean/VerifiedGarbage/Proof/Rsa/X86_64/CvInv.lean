module

-- separate module: the inverse's proofs import algebra, and `CvCheck` is imported by many modules
public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-!
# `vg_rsa_crt_values` on x86-64: `qInv`

`invPart` (`cvInv_ok`): `qInv = q⁻¹ mod p` by the batched divstep inverse,
and `gcd(q, p) = 1` and'ed into the mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `invPart`: `qInv` into `aX₂` and `gcd(q, p) = 1` and'ed into `sMask`,
for a mask that is set only if `p` is odd and above 1. -/
theorem cvInv_ok [InvLaw] {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {c : Bool}
    (hc : mword s.mem I.B = mask c)
    (hcP : c = true → wv s.mem I.B (slot (wk I.k) aP) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) :
    WP isa (seqs invPart) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mask (c && decide (Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k))
        (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) = 1)) ∧
      (c = true → ((wv s.mem I.B (slot (wk I.k) aP) (wk I.k) : Nat) : Int) ∣
          (wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) : Int) * wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) -
            Nat.gcd (wv s.mem I.B (slot (wk I.k) aQ) (wk I.k)) (wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
        wv t.mem I.B (slot (wk I.k) aX₂) (wk I.k) < wv s.mem I.B (slot (wk I.k) aP) (wk I.k)) ∧
      ∀ j, j = aP ∨ j = aQ ∨ j = aD → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hmw : ∀ {m m' : Mem} {j L' : Nat}, Outside I.B (slot (wk I.k) j) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ j _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) j (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have wvw : ∀ {m m' : Mem} {j : Nat}, j < 16 →
      wv m' I.B (slot (wk I.k) j) (wk I.k + 2) = wv m I.B (slot (wk I.k) j) (wk I.k + 2) →
      wv m' I.B (slot (wk I.k) j) (wk I.k) = wv m I.B (slot (wk I.k) j) (wk I.k) := fun {m m' j} _ e => by
    have e1 := wv_add m I.B (slot (wk I.k) j) (wk I.k) 2
    have e2 := wv_add m' I.B (slot (wk I.k) j) (wk I.k) 2
    have l1 := wv_lt m I.B (slot (wk I.k) j) (wk I.k)
    have l2 := wv_lt m' I.B (slot (wk I.k) j) (wk I.k)
    rw [e] at e2
    have := congrArg (· % 2 ^ (64 * wk I.k)) (e1.symm.trans e2)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
    exact this.symm
  -- The arrays a piece leaves: `ot j` from an `Outside` of another.
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [invPart, List.cons_append, List.nil_append]
  have hZ26 : slot (wk I.k) 26 ≤ I.Z := by
    have := slot_lin (wk I.k) 26; have := L.z; have := L.k1; unfold wk at *; omega
  have hw20 : wk I.k < 2 ^ 20 := by have := L.k2; unfold wk; omega
  -- The inverse.
  refine WP.seq (WP.mono (InvLaw.inverse_ok h.ws hZ26 hw20 (iU := aQ) (iV := aV) (iX₂ := aX₂) (iM := aP)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₈ ⟨_, f₈, k₈, hv₈⟩ => ?_)
  have e16 := slot_lin (wk I.k) 16
  have h₈ := h.step f₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Mut.ofSlot _ _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only
    · have := h.ws.sl (j := aV) (by decide); omega_arith
    · have := h.ws.sl (j := aX₂) (by decide); omega_arith
    · have := slot_lin (wk I.k) 26; omega_arith) k₈ (by decide)
  have f8 : ∀ j, j < 16 → j ≠ aV → j ≠ aX₂ →
      wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) := fun j hj h2 h4 =>
    f₈.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := slot_far (w := wk I.k) h2; omega_arith
      · have := slot_far (w := wk I.k) h4; omega_arith
      · have := slot_lt (w := wk I.k) hj; omega_arith) (by have := h.ws.sl hj; omega_arith)
  have hm₈ : mword s₈.mem I.B = mask c := by
    have e8 : mword s₈.mem I.B = mword s.mem I.B := f₈.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · have := hdr_lt_slot (wk I.k) aV (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) aX₂ (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith
      · have := hdr_lt_slot (wk I.k) 16 (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith)
      (by omega_arith)
    exact e8.trans hc
  -- `[c] := 1`, and the mask of `[v] = 1`.
  refine WP.seq (WP.mono (zeroA_ok h₈.ws (j := aC) (by decide)) fun s₉ ⟨z₉, o₉, k₉⟩ => ?_)
  have h₉ := h₈.arr (by decide) (Nat.le_refl _) o₉ k₉ (by decide)
  refine WP.seq (WP.mono (setOneA_ok h₉.ws (j := aC) (by decide)) fun s₁₀ ⟨m₁₀, k₁₀⟩ => ?_)
  have o₁₀ := writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by have := h.ws.sl (j := aC) (by decide); omega_arith)
  rw [← m₁₀] at o₁₀
  have h₁₀ := h₉.arr (by decide) (by omega_arith) o₁₀ k₁₀ (by decide)
  have vC : wv s₁₀.mem I.B (slot (wk I.k) aC) (wk I.k) = 1 := by
    rw [m₁₀, wv_low (by have := h.ws.w1; omega_arith), word_writeW_self,
      (writeW_outside s₉.mem I.B (1 : BitVec 64) (d := slot (wk I.k) aC) (by
        have := h.ws.sl (j := aC) (by decide); omega_arith)).wv (Or.inr (by omega_arith)) (by have := h.ws.sl (j := aC) (by decide); omega_arith)]
    have hz : ∀ q < wk I.k + 2, VG.Proof.Bignum.word s₉.mem I.B (slot (wk I.k) aC + 8 * q) = 0 :=
      (wv_eq_zero_iff _ _ _ _).mp z₉
    rw [wv_zero (n := wk I.k - 1) fun q hq => by
      have := hz (1 + q) (by omega_arith)
      rwa [show slot (wk I.k) aC + 8 * (1 + q) = slot (wk I.k) aC + 8 + 8 * q by omega_arith] at this]
    rfl
  have vV₁₀ : wv s₁₀.mem I.B (slot (wk I.k) aV) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) aV) (wk I.k) := by
    rw [ot o₁₀ (by omega_arith) (by decide) (by decide), ot o₉ (Nat.le_refl _) (by decide) (by decide)]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₁₀.ws (a := aV) (b := aC) (by decide) (by decide))
    fun s₁₁ ⟨hz₁₁, m₁₁, k₁₁⟩ => ?_)
  have h₁₁ := h₁₀.step (rs := []) (by rw [m₁₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁₁ (by decide)
  rw [vC, vV₁₀] at hz₁₁
  simp only [seqs]
  refine WP.mono (andZero_ok (c := c) h₁₁.ws (by rw [m₁₁]; exact (hmw o₁₀ (by omega_arith)).trans ((hmw o₉ (Nat.le_refl _)).trans hm₈)) hz₁₁)
    fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, hmt, at'⟩ := h₁₁.mask mt kt (by decide)
  have tX : ∀ j, j < 16 → j ≠ aC → wv t.mem I.B (slot (wk I.k) j) (wk I.k) = wv s₈.mem I.B (slot (wk I.k) j) (wk I.k) :=
    fun j hj hne => by
      rw [wvw hj (at' j hj), m₁₁, ot o₁₀ (by omega_arith) hne hj, ot o₉ (Nat.le_refl _) hne hj]
  refine ⟨ht, ?_, fun hcT => ?_, fun j hj => ?_⟩
  · rw [hmt]
    congr 1
    cases c
    · rfl
    · obtain ⟨hp, _⟩ := hcP rfl
      rw [(hv₈ hp).1]
  · obtain ⟨hp, _⟩ := hcP hcT
    obtain ⟨e1, e2, e3⟩ := hv₈ hp
    rw [tX aX₂ (by decide) (by decide)]
    exact ⟨e1 ▸ e2, e3⟩
  · have hj' : j < 16 := by rcases hj with rfl | rfl | rfl <;> decide
    rw [tX j hj' (by rcases hj with rfl | rfl | rfl <;> decide)]
    rcases hj with rfl | rfl | rfl
    · rw [f8 aP (by decide) (by decide) (by decide)]
    · rw [f8 aQ (by decide) (by decide) (by decide)]
    · rw [f8 aD (by decide) (by decide) (by decide)]

end VG.Proof.Rsa.X86_64
