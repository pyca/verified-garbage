module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Div

-- separate module: preparation of the CRT modulus is independent of the reduction algorithm

/-! # Preparing the CRT divisor independently of the reduction algorithm -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem cvDivisor_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat}
    (hj : j = aP ∨ j = aQ) :
    WP isa (seqs (divisor j)) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 →
        wv t.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1) ∧
      wv t.mem I.B (slot (wk I.k) aU) (wk I.k) = wv s.mem I.B (slot (wk I.k) aD) (wk I.k) ∧
      (∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k)) := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  have k1 := L.k1
  have eM : Impl.Bignum.X86_64.Public.sMask = 22 := rfl
  have hj16 : j < 16 := by rcases hj with rfl | rfl <;> decide
  have hjC : j ≠ aC := by rcases hj with rfl | rfl <;> decide
  have hjU : j ≠ aU := by rcases hj with rfl | rfl <;> decide
  have hmw : ∀ {m m' : Mem} {i L' : Nat}, Outside I.B (slot (wk I.k) i) L' m m' → L' ≤ 8 * (wk I.k + 2) →
      mword m' I.B = mword m I.B := fun {_ _ i _} o _ =>
    o.word (Or.inl (by have := hdr_lt_slot (wk I.k) i (show Impl.Bignum.X86_64.Public.sMask < 32 by decide); omega_arith))
      (by omega_arith)
  have ot : ∀ {m m' : Mem} {j i Ln : Nat}, Outside I.B (slot (wk I.k) j) Ln m m' → Ln ≤ 8 * (wk I.k + 2) → i ≠ j →
      i < 16 → wv m' I.B (slot (wk I.k) i) (wk I.k) = wv m I.B (slot (wk I.k) i) (wk I.k) :=
    fun o hL hij hi => outside_arr o hL hij (by omega_arith) hi hZ hn
  simp only [divisor, seqs]
  -- `[c] := [j]`, minus one.
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := aC) (by decide)) fun s₁ ⟨_, o₁, k₁⟩ => ?_)
  have h₁ := h.arr (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.seq (WP.mono (copyA_ok h₁.ws (o := aC) (a := j) (by decide) hj16 (Ne.symm hjC)) fun s₂ ⟨c₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.arr (by decide) (by omega_arith) o₂ k₂ (by decide)
  rw [ot o₁ (Nat.le_refl _) hjC hj16] at c₂
  -- The low word.
  have sC := h.ws.sl (j := aC) (by decide)
  refine WP.seq (WP.mono (decA_ok h₂.ws (j := aC) (by decide)) fun s₃ ⟨m₃, k₃⟩ => ?_)
  have o₃ := writeW_outside s₂.mem I.B (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1)
    (d := slot (wk I.k) aC) (by omega_arith)
  rw [← m₃] at o₃
  have h₃ := h₂.arr (by decide) (by omega_arith) o₃ k₃ (by decide)
  -- `[c] = [j] - 1` for an odd `[j]`.
  have vC₃ : wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) % 2 = 1 →
      wv s₃.mem I.B (slot (wk I.k) aC) (wk I.k) = wv s₂.mem I.B (slot (wk I.k) aC) (wk I.k) - 1 := by
    have w1 := h.ws.w1
    have e3 := wv_low (m := s₃.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have e2 := wv_low (m := s₂.mem) (B := I.B) (e := slot (wk I.k) aC) (w := wk I.k) (by omega_arith)
    have hw3 : VG.Proof.Bignum.word s₃.mem I.B (slot (wk I.k) aC) =
        VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1 := by
      rw [m₃, word_writeW_self]
    have hup : wv s₃.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) = wv s₂.mem I.B (slot (wk I.k) aC + 8) (wk I.k - 1) := by
      rw [m₃]; exact (writeW_outside s₂.mem I.B _ (by omega_arith)).wv (Or.inr (by omega_arith)) (by omega_arith)
    intro ho
    rw [e2] at ho ⊢
    have hodd : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat % 2 = 1 := by omega_arith
    have hsub : (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC) - 1).toNat =
        (VG.Proof.Bignum.word s₂.mem I.B (slot (wk I.k) aC)).toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_arith)]; rfl
    rw [e3, hup, hw3, hsub]
    omega_arith
  rw [c₂] at vC₃
  -- `[u] := d`.
  refine WP.seq (WP.mono (zeroA_ok h₃.ws (j := aU) (by decide)) fun s₄ ⟨_, o₄, k₄⟩ => ?_)
  have h₄ := h₃.arr (by decide) (Nat.le_refl _) o₄ k₄ (by decide)
  refine WP.mono (copyA_ok h₄.ws (o := aU) (a := aD) (by decide) (by decide) (by decide)) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have h₅ := h₄.arr (by decide) (by omega_arith) o₅ k₅ (by decide)
  have back : ∀ i, i < 16 → i ≠ aC → i ≠ aU → wv s₅.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k) :=
    fun i hi h1 h2 => by
      rw [ot o₅ (by omega_arith) h2 hi, ot o₄ (Nat.le_refl _) h2 hi, ot o₃ (by omega_arith) h1 hi, ot o₂ (by omega_arith) h1 hi,
        ot o₁ (Nat.le_refl _) h1 hi]
  refine ⟨h₅, ?_, fun ho => ?_, ?_, fun i hi => ?_⟩
  · exact (hmw o₅ (by omega_arith)).trans ((hmw o₄ (Nat.le_refl _)).trans ((hmw o₃ (by omega_arith)).trans
      ((hmw o₂ (by omega_arith)).trans (hmw o₁ (Nat.le_refl _)))))
  · rw [ot o₅ (by omega_arith) (by decide) (by decide), ot o₄ (Nat.le_refl _) (by decide) (by decide)]
    exact vC₃ ho
  · rw [c₅, ot o₄ (Nat.le_refl _) (by decide) (by decide), ot o₃ (by omega_arith) (by decide) (by decide),
      ot o₂ (by omega_arith) (by decide) (by decide), ot o₁ (Nat.le_refl _) (by decide) (by decide)]
  · exact back i (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.Rsa.X86_64
