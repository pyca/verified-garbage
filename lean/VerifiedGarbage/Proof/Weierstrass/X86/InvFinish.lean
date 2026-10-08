import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.X86.InvSpec

/-! # Final multiplication by the signed divstep correction -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem finish_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat}
    (hs : Scr s base size) (L : InvLay P size) (hOk : InvOk P p)
    (hp256 : p < 2 ^ 256) (hC : P.C < p) (hCn : P.Cn < p) :
    WP isa P.finish s fun z =>
      val32 z.mem base P.out 8 < p ∧
      val32 z.mem base P.out 8 * 2 ^ 256 % p =
        val32 s.mem base P.sA 8 * (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) % p ∧
      Keeps clob s z ∧ Unch base (invW P) s.mem z.mem := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hto := L.tbl_own; have hoo := L.out_own
  have hsz := L.size_eq
  have hk := hOk.k; have hfm := hOk.fm
  unfold InvCfg.finish
  refine WP.seq (WP.mono (finishPrep_ok hs ht (Nat.lt_trans hC hp256) (Nat.lt_trans hCn hp256))
    fun s₁ ⟨C₁, K₁, O₁⟩ => ?_)
  have hs₁ : Scr s₁ base 8192 := hsz ▸ hs.of_keeps K₁ (by decide)
  refine WP.mono (Mont.mulCall_ok hOk.fn hs₁ (o := P.out) (a := P.sA) (b := P.sNF)
    (by rw [hk]; exact hoo) (by rw [hk]; simp only [InvCfg.sA]; omega)
    (by rw [hk]; simp only [InvCfg.sNF]; omega) (by
      rw [hk, hfm, wordsVal_eq_val32, C₁]
      split <;> omega)) fun z ⟨K₂, V₂, E₂⟩ => ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hk, hfm, wordsVal_eq_val32] using V₂
  · simp only [hk, hfm, wordsVal_eq_val32] at E₂
    rw [C₁, O₁.val32 (by simp only [InvCfg.sA, InvCfg.sNF]; omega)
      (by simp only [InvCfg.sA]; omega)] at E₂
    exact E₂
  · exact K₁.trans ⟨fun r hr => K₂.gpr r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide), K₂.rd, K₂.wr⟩
  · have U₂ := K₂.mem
    simp only [Mont.callW, hk] at U₂
    intro x hx
    have ht' := hx (P.tbl, 320) (by simp [invW])
    rw [U₂ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx (P.out, 32) (by simp [invW]), hx (Mont.own 4, 256) (by simp [invW]),
        hx Mont.outW (by simp [invW])⟩),
      O₁ x (by simp only [InvCfg.sNF]; omega)]

end VG.Proof.Weierstrass.X86.Inv
