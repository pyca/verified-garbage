module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordDivisor
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast

-- separate module: frames the low-level reducer writes independently of the public guard

/-! # Word reductions preserve the RSA construction state and rejection mask -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The common path needs a normalized factor only when the output mask accepts it. -/
theorem cvWordFast_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat}
    (hj : j = aP ∨ j = aQ) (hW : 4 ≤ wk I.k) (hZ : slot (wk I.k) 17 ≤ I.Z)
    (hf : mword s.mem I.B = mask true →
      wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 ∧
      2 ^ (64 * (wk I.k / 2) - 1) ≤ wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 ∧
      wv s.mem I.B (slot (wk I.k) j) (wk I.k) < 2 ^ (64 * (wk I.k / 2))) :
    WP isa (.seq (seqs (divisor j)) (.seq (.block VG.Impl.Rsa.X86_64.WordDivide.normalize)
      VG.Impl.Rsa.X86_64.WordDivide.code)) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (mword s.mem I.B = mask true → wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
        wv s.mem I.B (slot (wk I.k) aD) (wk I.k) %
          (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      (∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k)) := by
  have hn := h.ws.scr.nowrap
  have W := wk I.k
  refine WP.seq (WP.mono (cvDivisor_ok h L hj) fun s₁ ⟨h₁, m₁, c₁, _, p₁⟩ => ?_)
  refine WP.mono (WordDivide.fast_ok h₁.ws hZ hW) fun t ⟨v, ff, kk⟩ => ?_
  have bound : ∀ r ∈ WordDivide.normRanges (wk I.k), r.1 + r.2 ≤ I.Z := by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ hr
  have ht := h₁.step ff (by
    intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr) bound kk (by decide)
  have m2 : mword t.mem I.B = mword s₁.mem I.B := ff.word_eq (by
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR, VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith) (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
  refine ⟨ht, m2.trans m₁, fun hc => ?_, fun i hi => ?_⟩
  · obtain ⟨ho, hlo, hhi⟩ := hf hc
    have C := c₁ ho
    have Clow : wv s₁.mem I.B (slot (wk I.k) aC) (wk I.k / 2) =
        wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1 := by
      rw [wv_low_of_lt (v := wk I.k / 2) (w := wk I.k) (by omega_arith) (by rw [C]; omega_using [hhi]), C]
    have htop := WordDivide.top_of_bound (m := s₁.mem) (B := I.B) (e := slot (wk I.k) aC) (n := wk I.k / 2) (by omega_using [hW]) (by rw [Clow]; exact hlo)
    have vv := v htop
    change wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
      wv s₁.mem I.B (slot (wk I.k) aD) (wk I.k) % wv s₁.mem I.B (slot (wk I.k) aC) (wk I.k / 2) at vv
    rw [Clow, p₁ aD (by simp)] at vv
    exact vv
  · rw [← p₁ i hi]
    apply ff.wv_eq _ (by have := h.ws.sl (j := i) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide); omega_arith)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR, VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, VG.Impl.Rsa.X86_64.Keys.CrtValues.aP, VG.Impl.Rsa.X86_64.Keys.CrtValues.aQ, VG.Impl.Rsa.X86_64.Keys.CrtValues.aD, aX₁, aX₂, slot] <;> omega_arith

end VG.Proof.Rsa.X86_64
