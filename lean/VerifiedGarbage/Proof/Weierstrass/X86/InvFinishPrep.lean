import VerifiedGarbage.Proof.Weierstrass.X86.InvState
import VerifiedGarbage.Proof.Weierstrass.X86.InvSignMask

/-! # Selecting the final Montgomery correction from the sign of f -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

local macro "apart" : tactic => `(tactic|
  ((try simp only [InvCfg.sF, InvCfg.sNF, InvCfg.sNG]) <;> omega))

theorem finishPrep_ok {P : InvCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size)
    (hC : P.C < 2 ^ 256) (hCn : P.Cn < 2 ^ 256) :
    WP isa (.block (setConst 4 P.sNF P.C ++ setConst 4 P.sNG P.Cn ++
      VG.Impl.Weierstrass.X86.Inv.maskOf P.sF ++ sel 8 P.sNF P.sNF P.sNG)) s fun z =>
      val32 z.mem base P.sNF 8 = (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) ∧
      Keeps clob s z ∧ Outside base P.sNF 68 s.mem z.mem := by
  have hn := hs.nowrap
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (setConst_ok hs (o := P.sNF) (by apart) hC) fun s₁ ⟨C₁, K₁, O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (o := P.sNG) (by apart) hCn) fun s₂ ⟨C₂, K₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (maskOf_ok hs₂ (coefficient := P.sF) (by apart)) fun s₃ ⟨C₃, K₃, M₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  rw [O₂.w32 (by apart) (by apart), O₁.w32 (by apart) (by apart)] at C₃
  refine WP.mono (sel_ok (decide (2 ^ 31 ≤ w32 s.mem base P.sF)) 8 hs₃
    (by simpa only [decide_eq_true_eq] using C₃) (o := P.sNF) (a := P.sNF) (b := P.sNG)
    (by apart) (by apart) (by apart) (by apart) (by apart)) fun z ⟨V, K₄, O₄⟩ => ⟨?_, ?_, ?_⟩
  · rw [wordsVal_eq_val32] at C₁ C₂
    rw [V, M₃, C₂, O₂.val32 (by apart) (by apart), C₁]
    simp only [decide_eq_true_eq]
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
      (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · intro x hx
    simp only [InvCfg.sNF] at hx
    rw [O₄ x (by apart), M₃, O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv
