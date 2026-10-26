module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrectionGeometry
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrectionNumerator
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidenCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic

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
