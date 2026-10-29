module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDProduct
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrectionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

import VerifiedGarbage.Proof.Rsa.WordRanges
import VerifiedGarbage.Proof.RsaKeyGen.X86.ProductCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidenCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
/-! # Result arithmetic preserves the already-computed inverse status -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyCorrectionNumerator.lean`, which only this module imported.
section

/-! # Form the correction's exact 128-bit numerator with native products -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem correctionNumerator_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128) :
    WP isa (correctionNumerator n) s fun t =>
      Ws t B Z n 32 ∧ Outs B correctionScratch s.mem t.mem ∧
      val32 t.mem B (arr 4 0) 4 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := h.workspace.nowrap
  have fr := h.arr_fit (j := aV) (by decide)
  have ft := h.arr_fit (j := aDen) (by decide)
  have bank := correction_workspace h
  have hz : 256 ≤ Z := bank.fits
  have L : Product.Layout Z 2 2 (arr 4 1) (arr n aV) (arr n aDen) kProduct := by
    refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [arr, S, aV, aDen, kProduct, hdr] at *
    all_goals omega_arith
  unfold correctionNumerator seqs
  refine WP.seq (WP.mono (Product.correct h.workspace L) fun u ⟨Ou, V, Ku⟩ => ?_)
  change Outs B [(kProduct, 4), (arr 4 1, 24)] s.mem u.mem at Ou
  change val32 u.mem B (arr 4 1) 6 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 at V
  have low : num u.mem B 4 1 = val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 4 ≤ 6) (by rw [V]; omega_arith)).trans V
  have hu := correction_workspace (h.rest Ku)
  refine WP.seq (WP.mono (constArray_ok hu (by decide) (by decide : 1 < 2 ^ 128))
    fun v ⟨hv, Ov, one, Kv⟩ => ?_)
  have productV : val32 v.mem B (arr 4 1) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 := by
    have H := Ov.num (j := 1) (by decide) (by simp) (hu.fit64 (by decide))
    exact H.trans low
  refine WP.mono (chainAddW_ok hv.workspace (by decide : 0 < 4)
    (by change 176 ≤ Z; omega_arith) (by change 200 ≤ Z; omega_arith) (by change 224 ≤ Z; omega_arith)
    (by decide) (by decide)) fun t ⟨Ot, ⟨carry, _, sum⟩, Kt⟩ => ?_
  change Outside B (arr 4 0) 16 v.mem t.mem at Ot
  change val32 t.mem B (arr 4 0) 4 + 2 ^ 128 * carry.toNat =
    val32 v.mem B (arr 4 1) 4 + val32 v.mem B (arr 4 2) 4 at sum
  rw [productV] at sum
  change val32 v.mem B (arr 4 2) 4 = 1 at one
  rw [one] at sum
  have result : val32 t.mem B (arr 4 0) 4 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 := by
    cases carry <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at sum <;> omega_arith
  have rest := Ku.trans ((Kv.mono (by decide)).trans (Kt.mono (by decide)))
  refine ⟨h.rest rest, ?_, result, rest⟩
  have first : Outs B correctionScratch s.mem u.mem := by
    apply VG.Proof.Rsa.outs_cover Ou
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(kProduct, 4), by simp [correctionScratch], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(hdr, 96), by simp [correctionScratch], by decide, by decide⟩
  exact (first.trans (correction_scratch_keep (by decide) Ov)).trans
    (correction_scratch_outside (by decide) (by decide) Ot)

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyCorrection.lean`, which only this module imported.
section

/-! # Exact small correction for the quotient-based private exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def correctionRanges (n : Nat) : List (Nat × Nat) := correctionScratch ++ [(arr n aV, S n)]

theorem correction_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (positive : 0 < val32 s.mem B kEv 2)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128)
    (quotientFits : (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
      val32 s.mem B kEv 2 < 2 ^ 64) :
    WP isa (correction n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (correctionRanges n) s.mem t.mem ∧
      num t.mem B n aV = (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
        val32 s.mem B kEv 2 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hn := h.workspace.nowrap
  unfold correction seqs
  refine WP.seq (WP.mono (correctionNumerator_ok h width fits) fun u ⟨hu, Ou, numerator, Ku⟩ => ?_)
  have h4 := correction_workspace hu
  have hz : 256 ≤ Z := h4.fits
  have E := correction_preserves_exponent Ou
  refine WP.seq (WP.mono (widenCopy_ok h4 (by decide : 0 < 2) (by decide : 2 ≤ 4) (by decide)
    (by change 88 ≤ Z; omega) (Or.inl (by decide))) fun v ⟨hv, Ov, fullDivisor, _, Kv⟩ => ?_)
  change Outside B (arr 4 2) (S 4) u.mem v.mem at Ov
  change val32 v.mem B (arr 4 2) 6 = val32 u.mem B kEv 2 at fullDivisor
  rw [E] at fullDivisor
  have numeratorV : (divisionGeometry B Z 4).value v.mem 0 =
      val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 := by
    change val32 v.mem B (arr 4 0) 4 = _
    exact (Ov.val32 (by decide) (by decide)).trans numerator
  have divisorV : (divisionGeometry B Z 4).value v.mem 2 = val32 s.mem B kEv 2 := by
    have bound : val32 v.mem B (arr 4 2) 6 < 2 ^ (32 * 5) := by
      rw [fullDivisor]
      exact Nat.lt_of_lt_of_le (val32_lt s.mem B kEv 2) (Nat.pow_le_pow_right (by decide) (by decide))
    exact (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 5 ≤ 6) bound).trans fullDivisor
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok (division_context hv))
    fun w ⟨_, Ow, Kw, computed⟩ => ?_)
  have result := computed (by rw [divisorV]; exact positive)
    (by
      rw [divisorV]
      exact Nat.lt_of_lt_of_le (val32_lt s.mem B kEv 2)
        (Nat.pow_le_pow_right (by decide) (by change 64 ≤ 128; decide)))
  rw [numeratorV, divisorV] at result
  have quotient := result.2
  change val32 w.mem B (arr 4 0) 4 = _ at quotient
  have quotientLow : val32 w.mem B (arr 4 0) 2 =
      (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) / val32 s.mem B kEv 2 :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by decide : 2 ≤ 4) (by rw [quotient]; exact quotientFits)).trans quotient
  have hw := (hu.rest Kv).rest Kw
  have endSmall : arr 4 0 + 8 ≤ arr n aV := by unfold arr S aV hdr; omega
  refine WP.mono (widenCopy_ok hw (by decide : 0 < 2) width (by decide)
    (by change 168 ≤ Z; omega) (Or.inl endSmall)) fun t ⟨ht, Ot, _, value, Kt⟩ => ?_
  have changed : Outside B hdr 96 v.mem w.mem := division_frame Ow
  have scratch : Outs B correctionScratch s.mem w.mem :=
    (Ou.trans (correction_scratch_arr (by decide) Ov)).trans
      (correction_scratch_outside (Nat.le_refl _) (Nat.le_refl _) changed)
  refine ⟨ht, ?_, value.trans quotientLow,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kw.trans (Kt.mono (by decide))))⟩
  exact (scratch.mono (fun r hr => List.mem_append_left _ hr)).trans
    (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def exponentResultRanges (n : Nat) : List (Nat × Nat) :=
  (kProduct, 4) :: (hdr, 15 * S n) :: ranges n exponentArrays []

theorem exponent_result_frame {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (exponentResultRanges n) m m') : Outs B (exponentRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact ⟨(kOk, 68), by simp [exponentRanges, exponentTemps], by decide, by decide⟩
  · exact ⟨(hdr, 15 * S n), by simp [exponentRanges, exponentTemps], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨r, List.mem_append_right _ array, Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_header {m m' : Mem} {B : Addr} {n d count : Nat}
    (bound : d + 4 * count ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    val32 m' B d count = val32 m B d count := by
  apply O.val32 _ (by unfold kProduct at bound; omega)
  intro r hr
  simp only [exponentResultRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | array
  · exact Or.inl bound
  · exact Or.inl (Nat.le_trans bound (by decide : kProduct ≤ hdr))
  · simp only [ranges, List.map_nil, List.append_nil, List.mem_map] at array
    obtain ⟨a, _, rfl⟩ := array
    have lower : hdr ≤ arr n a := Nat.le_add_right ..
    exact Or.inl (Nat.le_trans bound (Nat.le_trans (by decide : kProduct ≤ hdr) lower))

theorem exponent_result_slot {m m' : Mem} {B : Addr} {n d : Nat}
    (bound : d + 4 ≤ kProduct) (O : Outs B (exponentResultRanges n) m m') :
    slot m' B d = slot m B d := by
  have H := exponent_result_header (count := 1) bound O
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem exponent_result_complement {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outside B (arr n aDen) (S n) m m') : Outs B (exponentResultRanges n) m m' :=
  Outs.of_outside O (by simp [exponentResultRanges, ranges, exponentArrays])

theorem correction_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (persistent : 15 ≤ j) (unchanged : j ≠ aV) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (correctionRanges n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · have lower : hdr ≤ arr n j := Nat.le_add_right ..
    exact Or.inr (Nat.le_trans (by decide : kProduct + 4 ≤ hdr) lower)
  · have lower : 256 ≤ arr n 15 :=
      Nat.le_trans (by decide : 256 ≤ 160 + 15 * (4 * 2))
        (Nat.add_le_add_left (Nat.mul_le_mul_left 15 (Nat.mul_le_mul_left 4 (Nat.le_add_left 2 n))) 160)
    exact Or.inr (Nat.le_trans lower (arr_mono persistent))
  · have D := arr_disj (w := n) unchanged
    simp only at D ⊢
    unfold S at D ⊢
    omega

theorem exponent_result_correction {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (correctionRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [correctionRanges, correctionScratch, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨(kProduct, 4), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], Nat.le_refl _, ?_⟩
    unfold S
    omega
  · exact ⟨(arr n aV, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, Nat.le_refl _⟩

theorem exponent_result_product {m m' : Mem} {B : Addr} {n : Nat}
    (O : Outs B (dProductRanges n) m m') : Outs B (exponentResultRanges n) m m' := by
  apply VG.Proof.Rsa.outs_cover O
  intro r hr
  simp only [dProductRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨(kProduct, 4), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], ?_, ?_⟩
    · unfold arr
      omega
    · unfold arr S
      omega
  · exact ⟨(arr n aD, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, by unfold S; omega⟩

end VG.Proof.RsaKeyGen.X86.Key
