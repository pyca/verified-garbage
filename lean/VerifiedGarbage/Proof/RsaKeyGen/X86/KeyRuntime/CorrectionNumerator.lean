module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Product
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorrectionGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Small
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrectionGeometry
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.WordRanges
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Form the correction's exact 128-bit numerator with native products -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aV aDen kProduct)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem correctionNumerator_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (_width : 2 ≤ n)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128) :
    WP isa correctionNumerator s fun t =>
      Ws t B Z n 32 ∧ Outs B correctionScratch s.mem t.mem ∧
      val32 t.mem B (arr 4 0) 4 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.old.workspace.nowrap
  have fr := h.arr_fit (j := aV) (by decide)
  have ft := h.arr_fit (j := aDen) (by decide)
  have bank := VG.Proof.RsaKeyGen.X86.Key.correction_workspace h.old
  have hz : 256 ≤ Z := bank.fits
  have L : ProductGeometry Z 2 2 (arr 4 1) (arr n aV) (arr n aDen) := by
    refine ⟨⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp only [arr, S, aV, aDen, hdr] at *
    all_goals omega
  unfold correctionNumerator seqs
  refine WP.seq (WP.mono (product_ok (left := .exponent) (right := .exponent)
    (out := .array .correction 1) (a := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (b := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aDen) h L) fun u ⟨hu, Ou, V, Ku⟩ => ?_)
  change Outs B [(kProduct, 28), (arr 4 1, 24)] s.mem u.mem at Ou
  change val32 u.mem B (arr 4 1) 6 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 at V
  have low : num u.mem B 4 1 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 4 ≤ 6) (by rw [V]; omega)).trans V
  refine WP.seq (WP.mono (small_ok (j := 2) hu .correction 1 (by change 232 ≤ Z; omega))
    fun v ⟨hv, Ov, wideOne, Kv⟩ => ?_)
  change Outside B (arr 4 2) 24 u.mem v.mem at Ov
  change val32 v.mem B (arr 4 2) 6 = 1 at wideOne
  have one : val32 v.mem B (arr 4 2) 4 = 1 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 4 ≤ 6)
      (by rw [wideOne]; decide)).trans wideOne
  have productV : val32 v.mem B (arr 4 1) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 :=
    (Ov.val32 (by decide) (by decide)).trans low
  refine WP.mono (chainAddW_ok hv.old.workspace (by decide : 0 < 4)
    (by change 176 ≤ Z; omega) (by change 200 ≤ Z; omega) (by change 224 ≤ Z; omega)
    (by decide) (by decide)) fun t ⟨Ot, ⟨carry, _, sum⟩, Kt⟩ => ?_
  change Outside B (arr 4 0) 16 v.mem t.mem at Ot
  change val32 t.mem B (arr 4 0) 4 + 2 ^ 128 * carry.toNat =
    val32 v.mem B (arr 4 1) 4 + val32 v.mem B (arr 4 2) 4 at sum
  rw [productV] at sum
  change val32 v.mem B (arr 4 2) 4 = 1 at one
  rw [one] at sum
  have result : val32 t.mem B (arr 4 0) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 := by
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at sum <;> omega
  have rest := Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  have frame : Outs B correctionScratch s.mem t.mem := by
    have first : Outs B correctionScratch s.mem u.mem := VG.Proof.Rsa.outs_cover Ou (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(kProduct, 28), by simp [correctionScratch], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(hdr, 96), by simp [correctionScratch], by decide, by decide⟩)
    exact (first.trans (correction_scratch_arr (by decide) Ov)).trans
      (correction_scratch_outside (by decide) (by decide) Ot)
  refine ⟨h.keep rest (VG.Proof.Rsa.X86.KeyRt.outs_outside frame ?_), frame, result, rest.mono (by decide)⟩
  intro region member
  simp only [correctionScratch, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only [kProduct, hdr] <;> omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
