import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # Final multiplication by the signed divstep correction -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem finishLayout {P : InvCfg} {size : Nat} (L : InvLay P size) :
    OpLay P.M size P.wk P.out P.sA P.sNF := by
  have ht := L.tbl_bound; have hw := L.wk_bound; have ho := L.out_bound
  have hwt := L.wk_tbl; have hwo := L.wk_out; have hwm := L.wk_mod
  have hwtmp := L.wk_tmp; have hotmp := L.out_tmp
  constructor <;> (try simp only [accLen, words, L.n4, InvCfg.sA, InvCfg.sNF]) <;> omega

theorem finish_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat}
    (hs : Scr s base size) (L : InvLay P size) (hM : ModOkW P.M size p s.mem base)
    (hp256 : p < 2 ^ 256) (hC : P.C < p) (hCn : P.Cn < p) :
    WP isa P.finish s fun z =>
      val32 z.mem base P.out 8 < p ∧
      val32 z.mem base P.out 8 * 2 ^ 256 % p =
        val32 s.mem base P.sA 8 * (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) % p ∧
      Keeps clob s z ∧
      Unch base [(P.tbl, 320), (P.out, 32), (P.M.tmp, 32), (P.wk, 68)] s.mem z.mem := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hm := L.mod_bound; have htm := L.tbl_mod
  unfold InvCfg.finish
  refine WP.seq (WP.mono (finishPrep_ok hs ht (Nat.lt_trans hC hp256) (Nat.lt_trans hCn hp256))
    fun s₁ ⟨C₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have M₁ : ModOkW P.M size p s₁.mem base := by
    refine ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
    rw [L.n4, wordsVal_eq_val32, O₁.val32 (by simp only [InvCfg.sNF]; omega) (by omega)]
    simpa only [L.n4, wordsVal_eq_val32] using hM.val
  refine WP.mono (mul_ok hs₁ M₁ (finishLayout L) (by
    rw [L.n4, wordsVal_eq_val32, C₁]
    split <;> omega)) fun z ⟨K₂, V₂, E₂⟩ => ⟨?_, ?_, ?_, ?_⟩
  · simpa only [L.n4, wordsVal_eq_val32] using V₂
  · simp only [L.n4, wordsVal_eq_val32] at E₂
    rw [C₁, O₁.val32 (by simp only [InvCfg.sA, InvCfg.sNF]; omega)
      (by simp only [InvCfg.sA]; omega)] at E₂
    exact E₂
  · exact K₁.trans ⟨K₂.gpr, K₂.rd, K₂.wr⟩
  · have U₂ := K₂.mem
    simp only [accLen, words, L.n4, Nat.reduceMul, Nat.reduceAdd] at U₂
    intro x hx
    have ht' := hx (P.tbl, 320) (by simp)
    rw [U₂ x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx (P.out, 32) (by simp), hx (P.M.tmp, 32) (by simp), hx (P.wk, 68) (by simp)⟩),
      O₁ x (by simp only [InvCfg.sNF]; omega)]

end VG.Proof.Weierstrass.X86.Inv
