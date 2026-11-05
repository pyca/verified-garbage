module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowInputs
public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowResult
import VerifiedGarbage.Proof.Rsa.X86_64.WordFast

/-! # A complete word remainder in the CRT validation workspace -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ranges (w : Nat) : List (Nat × Nat) := [(slot w CheckKey.aR, 8 * w), (start w, span w)]

theorem norm_bound {w : Nat} (hw : 4 ≤ w) {r : Nat × Nat}
    (hr : r ∈ VG.Proof.Rsa.X86_64.WordDivide.normRanges w) : r.1 + r.2 ≤ span w := by
  simp only [VG.Proof.Rsa.X86_64.WordDivide.normRanges, VG.Proof.Rsa.X86_64.WordDivide.allRanges,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [WordDivide.aM, WordDivide.aR, WordDivide.aT, WordDivide.aV, span, slot] <;> omega_using [hw]

theorem norm_mut {w : Nat} {r : Nat × Nat} (hr : r ∈ VG.Proof.Rsa.X86_64.WordDivide.normRanges w) :
    VG.Proof.Rsa.X86_64.Mut r := by
  simp only [VG.Proof.Rsa.X86_64.WordDivide.normRanges, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact VG.Proof.Rsa.X86_64.Mut.ofSlot _ _ _
  · exact VG.Proof.Rsa.X86_64.WordDivide.all_mut hr

/-- The reducer changes only its new workspace and the original remainder array. -/
theorem code_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (h : Good s B Z w minv)
    (hZ : start w + span w ≤ Z) (hw : 4 ≤ w) (hw' : w < 2 ^ 24) :
    WP isa WordValidation.code s fun t =>
      ((2 ^ (64 * (w / 2) - 1) ≤ wv s.mem B (slot w CheckKey.aM) w ∧
          wv s.mem B (slot w CheckKey.aM) w < 2 ^ (64 * (w / 2))) →
        wv t.mem B (slot w CheckKey.aR) w =
          wv s.mem B (slot w aAcc) w % wv s.mem B (slot w CheckKey.aM) w) ∧
      Frm B (ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hp : 0 < span w := by simp only [span, slot, hdrBytes]; omega_arith
  have outR : slot w CheckKey.aR + 8 * w ≤ start w := by simp only [start, slot, CheckKey.aR]; omega_arith
  have srcR : start w + slot w WordDivide.aR + 8 * w ≤ start w + span w := by
    simp only [span, slot, WordDivide.aR]; omega_arith
  unfold WordValidation.code
  change WP isa (.seq WordValidation.inputs (.seq (.seq (.block WordDivide.normalize) WordDivide.code)
    (.seq (.block WordValidation.resultSetup) copyWords))) s _
  refine WP.seq (WP.mono (inputs_ok h hZ hw hw') fun t₁ ⟨ws₁, D₁, M₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.WordDivide.fast_ok ws₁ (Nat.le_refl _) hw)
    fun t₂ ⟨v₂, f₂, k₂⟩ => ?_)
  have ws₂ := ws₁.congr f₂ (fun _ hr => norm_mut hr) k₂ (by decide)
  have o₂ : Outside B (start w) (span w) t₁.mem t₂.mem :=
    outside_view (by omega_using [hn, hZ]) hp (InScr.of_frm f₂ (fun _ hr => norm_bound hw hr))
  have o02 := o₁.trans o₂
  have k02 := k₁.trans k₂
  have hs₂ := h.scr.congr k02.2.2
  refine WP.seq (WP.mono (resultSetup_ok ws₂) fun t₃ ⟨hdi₃, hsi₃, hbx₃, h12₃, m₃, k₃⟩ => ?_)
  have k03 := k02.trans k₃
  refine WP.mono (copy_ok (w := w) (h.scr.congr k03.2.2) hsi₃ hbx₃ h12₃
    (by omega_using [hw]) (by omega_using [hw']) (by omega_using [srcR, hZ])
    (by omega_using [outR, hZ]) (Or.inr (by omega_using [outR]))) fun t ⟨vR, oR, k₄⟩ => ?_
  have kk : Keep (.rdi :: mmRegs) s t := (k03.trans k₄).mono (by decide)
  refine ⟨fun hM => ?_, ?_, restore_base kk ((k₄.gpr (by decide)).trans (hdi₃.trans h.rdi.symm))⟩
  · have mpos : 0 < wv s.mem B (slot w CheckKey.aM) w := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hM.1
    have Mlow : wv t₁.mem (off B (start w)) (slot w WordDivide.aM) (w / 2) =
        wv s.mem B (slot w CheckKey.aM) w := by
      rw [VG.Proof.Rsa.X86_64.wv_low_of_lt (v := w / 2) (w := w) (by omega_arith) (by rw [M₁]; exact hM.2), M₁]
    have top := VG.Proof.Rsa.X86_64.WordDivide.top_of_bound (m := t₁.mem) (B := off B (start w))
      (e := slot w WordDivide.aM) (n := w / 2) (by omega_using [hw]) (by rw [Mlow]; exact hM.1)
    have vv := v₂ top
    rw [D₁, Mlow] at vv
    have hpow : 2 ^ (64 * (w / 2)) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have hlt : wv t₂.mem (off B (start w)) (slot w WordDivide.aR) (w + 1) < 2 ^ (64 * w) := by
      rw [vv]; exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ mpos) hM.2) hpow
    rw [vR, m₃, ← wv_view t₂.mem B (start w) (slot w WordDivide.aR) w,
      VG.Proof.Rsa.X86_64.wv_low_of_lt (v := w) (w := w + 1) (by omega_arith) hlt, vv]
  · have o03 : Outside B (start w) (span w) s.mem t₃.mem := by rw [m₃]; exact o02
    exact (Frm.of_outside o03 (by simp [ranges])).trans (Frm.of_outside oR (by simp [ranges]))

end VG.Proof.Rsa.X86_64.WordValidation
