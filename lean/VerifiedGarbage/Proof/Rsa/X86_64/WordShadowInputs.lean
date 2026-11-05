module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowCopy
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- separate module: compose input copies separately from reducer execution and result recovery

/-! # Copying the validation product and modulus into the word reducer -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem inputs_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (h : Good s B Z w minv)
    (hZ : start w + span w ≤ Z) (hw : 4 ≤ w) (hw' : w < 2 ^ 24) :
    WP isa WordValidation.inputs s fun t =>
      VG.Proof.Rsa.X86_64.Ws t (off B (start w)) (span w) w ∧
      wv t.mem (off B (start w)) (slot w WordDivide.aD) w = wv s.mem B (slot w aAcc) w ∧
      wv t.mem (off B (start w)) (slot w WordDivide.aM) w = wv s.mem B (slot w CheckKey.aM) w ∧
      Outside B (start w) (span w) s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn := h.scr.nowrap
  have srcD : slot w aAcc + 8 * w ≤ start w := by simp only [start, slot, aAcc]; omega_arith
  have srcM : slot w CheckKey.aM + 8 * w ≤ start w := by simp only [start, slot, CheckKey.aM]; omega_arith
  have dstD : start w + slot w WordDivide.aD + 8 * w ≤ start w + span w := by
    simp only [slot, WordDivide.aD, span]; omega_arith
  have dstM : start w + slot w WordDivide.aM + 8 * w ≤ start w + span w := by
    simp only [slot, WordDivide.aM, span]; omega_arith
  have hdD : start w + 256 ≤ start w + slot w WordDivide.aD := by simp only [slot, hdrBytes]; omega_arith
  have hdM : start w + 256 ≤ start w + slot w WordDivide.aM := by simp only [slot, hdrBytes]; omega_arith
  unfold WordValidation.inputs
  change WP isa (.seq (.block WordValidation.enter) (.seq (.block setBases)
    (.seq (.block WordValidation.productSetup) (.seq copyWords (.seq (.block WordValidation.modulusSetup) copyWords))))) s _
  apply WP.assoc
  refine WP.seq (WP.mono (setup_ok h hZ hw hw') fun t₁ ⟨ws₁, hsi₁, h10₁, h12₁, h9₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.base_ok WordDivide.aD (r := .rbx) (by decide) ws₁.rdi h9₁)
    fun t₂ ⟨hbx₂, m₂, k₂⟩ => ?_)
  have ws₂ := ws_same ws₁ m₂ k₂ (by decide)
  have k02 := k₁.trans k₂
  refine WP.seq (WP.mono (copy_ok (w := w) (eD := start w + slot w WordDivide.aD) (h.scr.congr k02.2.2) ((k₂.gpr (by decide)).trans hsi₁)
    (by rw [hbx₂, addr_view]) ((k₂.gpr (by decide)).trans h12₁) (by omega_using [hw]) (by omega_using [hw'])
    (by omega_using [srcD, hZ]) (by omega_using [dstD, hZ]) (Or.inl (by omega_using [srcD])))
    fun t₃ ⟨vD, oD, k₃⟩ => ?_)
  have ws₃ := ws_after ws₂ hn hZ hdD oD k₃ (by decide)
  have o02 : Outside B (start w) (span w) s.mem t₂.mem := by rw [m₂]; exact o₁
  have o03 := o02.trans (widen oD (by omega_arith) dstD)
  have D₃ : wv t₃.mem (off B (start w)) (slot w WordDivide.aD) w = wv s.mem B (slot w aAcc) w := by
    rw [wv_view, vD, o02.wv (Or.inl srcD) (by omega_using [srcD, hZ, hn])]
  have k03 := k02.trans k₃
  refine WP.seq (WP.mono (modulusSetup_ok ws₃.rdi (((k₂.trans k₃).gpr (by decide)).trans h9₁)
    (((k₂.trans k₃).gpr (by decide)).trans h10₁)) fun t₄ ⟨hsi₄, hbx₄, m₄, k₄⟩ => ?_)
  have ws₄ := ws_same ws₃ m₄ k₄ (by decide)
  have k04 := k03.trans k₄
  refine WP.mono (copy_ok (w := w) (eD := start w + slot w WordDivide.aM) (h.scr.congr k04.2.2) hsi₄ (by rw [hbx₄, addr_view])
    (by rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), h12₁])
    (by omega_using [hw]) (by omega_using [hw']) (by omega_using [srcM, hZ])
    (by omega_using [dstM, hZ]) (Or.inl (by omega_using [srcM]))) fun t ⟨vM, oM, k₅⟩ => ?_
  have ws₅ := ws_after ws₄ hn hZ hdM oM k₅ (by decide)
  have o04 : Outside B (start w) (span w) s.mem t₄.mem := by rw [m₄]; exact o03
  refine ⟨ws₅, ?_, ?_, o04.trans (widen oM (by omega_arith) dstM), (k04.trans k₅).mono (by decide)⟩
  · rw [wv_view, oM.wv (Or.inl (by simp only [slot, WordDivide.aD, WordDivide.aM]; omega_arith))
      (by omega_using [dstD, hZ, hn]), m₄, ← wv_view, D₃]
  · rw [wv_view, vM, o04.wv (Or.inl srcM) (by omega_using [srcM, hZ, hn])]

end VG.Proof.Rsa.X86_64.WordValidation
