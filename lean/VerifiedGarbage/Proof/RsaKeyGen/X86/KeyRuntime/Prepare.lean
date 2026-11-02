module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Constant
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Inverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepared
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepareFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorrectionGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorrectionNumerator
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Widen
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrectionGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionGeometry
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DProduct
import VerifiedGarbage.Proof.Rsa.WordRanges
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Complement
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DEven
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
public import VerifiedGarbage.Spec.Rsa.Contract
/-! # The native factor, LCM, and private-inverse stages compose -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DOne.lean`, which only this module imported.
section

/-! # The unit public exponent at a runtime width -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD aOne aL kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem dOne_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (one : num s.mem B n aOne = 1) :
    WP isa dOne s fun t => Ws t B Z n 32 ∧
      Keep B n [aD, aT1] [sT, kFlag, kOk] s.mem t.mem ∧ num t.mem B n aD = 1 ∧
      slot t.mem B kOk = (if num s.mem B n aL = 1 then 0 else 1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold dOne seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide) (by decide)) fun u ⟨hu, Ou, D, Ku, _⟩ => ?_)
  rw [one] at D
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  have O : num u.mem B n aOne = 1 := by rw [Ou.num (by decide) (by simp) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (eq_ok hu (by decide) (by decide) (by decide) (by decide) (by decide) hf)
    fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [L, O] at flag
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (notSlot_ok hv (by decide) hf bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aD, aT1]) (ds := [sT, kFlag, kOk])).join Ot
    (js := [aD, aT1]) (ds := [sT, kFlag, kOk]), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  · rw [Ot.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; decide)
      (h.fit64 (by decide)), Ov.num (by decide) (by decide) (h.fit64 (by decide)), D]
  · rw [mask, flag]
    by_cases p : num s.mem B n aL = 1 <;> simp [p]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/LAtLeastTwo.lean`, which only this module imported.
section

/-! # The public-exponent inverse also needs an LCM of at least two -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem lAtLeastTwo_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kFlag ≤ 1) :
    WP isa lAtLeastTwo s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold lAtLeastTwo seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (2 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 2 at constant
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [L, constant] at subtract
  have iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  have flag : slot v.mem B kFlag = slot s.mem B kFlag := by
    rw [Ov.slot hf (by simp), Ou.slot hf (by simp)]
  refine WP.mono (borrowMask_ok hv borrow (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  have validMask : slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) := by
    simpa only [iffBorrow, flag] using value
  exact ⟨ht, (Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ot
    (js := [aT1, aT2]) (ds := [kOk]), validMask,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/OddPrepare.lean`, which only this module imported.
section

/-! # Prepare the private exponent using only a two-word inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aL aE aU aV aOne kEv kFlag kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (OddPrepared exponentRanges exponentTemps
  exponent_preserves_e exponent_preserves_num exponent_temps_inverse exponent_temps_keep
  exponent_temps_preserves_num exponent_mask_coefficient InverseLayout inverse_end_le)

theorem dOddPrepare_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dOddPrepare s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧
      OddPrepared B n (val32 s.mem B kEv 2) (num s.mem B n aL) t ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  have e3 : 3 ≤ e := large
  have eo : e % 2 = 1 := odd
  have e64 : e < 2 ^ 64 := val32_lt s.mem B kEv 2
  have re : L % e < e := Nat.mod_lt _ (by omega)
  unfold dOddPrepare seqs
  refine WP.seq (WP.mono (arrayDivision_ok h (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [loaded]; exact Nat.zero_lt_of_lt large)) fun u ⟨hu, Ou, Q, R, Ku⟩ => ?_)
  rw [loaded] at Q R
  change num u.mem B n aU = L / e at Q
  change num u.mem B n aV = L % e at R
  have divisionFrame := exponent_division_frame Ou
  have Eu : val32 u.mem B kEv 2 = e := exponent_preserves_e divisionFrame
  have remainderBound : val32 u.mem B (arr n aV) n < 2 ^ 64 := by
    change num u.mem B n aV < 2 ^ 64
    rw [R]
    exact Nat.lt_trans re e64
  have remainderLow : val32 u.mem B (arr n aV) 2 = L % e :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width remainderBound).trans R
  have layout : InverseLayout Z 2 (arr n aV) kEv := by
    have fit := hu.arr_fit (j := aV) (by decide)
    have head := hu.hdr_le
    refine ⟨?_, ?_, Or.inr (inverse_end_le width (by decide)), Or.inl (by decide)⟩
    · unfold S at fit
      omega
    · unfold kEv hdr at *
      omega
  refine WP.seq (WP.mono (inverseFrom_ok (w := .exponent)
    (src := VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV) (mo := .fixed kEv)
    hu (by decide) (by decide) layout
    (by change val32 u.mem B kEv 2 % 2 = 1; rw [Eu]; exact eo) (by change 1 < val32 u.mem B kEv 2; rw [Eu]; omega)) fun v ⟨hv, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  change num v.mem B 2 1 = Nat.gcd (val32 u.mem B (arr n aV) 2) (val32 u.mem B kEv 2) at gcd
  change (val32 u.mem B kEv 2 : Int) ∣ (num v.mem B 2 3 : Int) * val32 u.mem B (arr n aV) 2 - num v.mem B 2 1 at congruence
  rw [remainderLow, Eu] at gcd congruence
  rw [gcd] at congruence
  change num v.mem B 2 3 < val32 u.mem B kEv 2 at boundX
  rw [Eu] at boundX
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have inverseFrame : OutsS B (s.gpr .esp) (exponentTemps n) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => exponent_temps_inverse width) Ov
  refine WP.seq (WP.mono (gcdIsOne_ok (w := .exponent) hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  simp only [Width.words] at Ow
  change slot w.mem B kFlag = (if num v.mem B 2 1 = 1 then 1 else 0) at flag
  rw [gcd] at flag
  have coefficientW : num w.mem B 2 3 = num v.mem B 2 3 :=
    Ow.num (by decide) (by decide) (by simpa only [kw_words hv.width, Width.words] using
      (hv.runtime (w := .exponent) (by decide)).ws.fit64 (j := 3) (by decide))
  have compareFrame : Outs B (exponentTemps n) v.mem w.mem :=
    exponent_temps_keep width (by decide) (by decide) Ow
  have prefixFrame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem w.mem :=
    (OutsS.of_outs divisionFrame).trans ((inverseFrame.trans (OutsS.of_outs compareFrame)).mono
      (fun r hr => List.mem_append_left _ hr))
  have Lw : num w.mem B n aL = L :=
    h.read_num (by decide) prefixFrame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  have bit : slot w.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (lAtLeastTwo_ok hw bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  have maskFrame : Outs B (exponentTemps n) w.mem t.mem :=
    exponent_temps_keep (Nat.le_refl n) (by decide) (by decide) Ot
  have tailFrame := (inverseFrame.trans (OutsS.of_outs compareFrame)).trans (OutsS.of_outs maskFrame)
  have frame : OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem :=
    (OutsS.of_outs divisionFrame).trans (tailFrame.mono (fun r hr => List.mem_append_left _ hr))
  have coefficientT : num t.mem B 2 3 = num v.mem B 2 3 :=
    (exponent_mask_coefficient Ot).trans coefficientW
  have finalMask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    by_cases G : Nat.gcd (L % e) e = 1 <;> simpa [Lw, flag, G] using mask
  have tailOld : OutsS B (s.gpr .esp) (exponentTemps n) u.mem t.mem := tailFrame
  refine ⟨ht, frame, ⟨h.read_val32 (by decide) frame exponent_preserves_e, ?_, ?_, ?_, ?_, ?_, ?_, finalMask⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · exact h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans Q
  · exact (h.read_num (by decide) tailOld (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)))).trans R
  · rw [h.read_num (by decide) frame (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide))), one]
  · rw [coefficientT]
    exact boundX
  · rw [coefficientT]
    exact congruence

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Correction.lean`, which only this module imported.
section

/-! # Exact small correction for the quotient-based private exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aV aDen kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (correction_workspace divisionGeometry division_context division_frame)

def correctionRanges (n : Nat) : List (Nat × Nat) := correctionScratch ++ [(arr n aV, S n)]

theorem correction_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (positive : 0 < val32 s.mem B kEv 2)
    (fits : val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1 < 2 ^ 128)
    (quotientFits : (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
      val32 s.mem B kEv 2 < 2 ^ 64) :
    WP isa correction s fun t =>
      Ws t B Z n 32 ∧ Outs B (correctionRanges n) s.mem t.mem ∧
      num t.mem B n aV = (val32 s.mem B (arr n aV) 2 * val32 s.mem B (arr n aDen) 2 + 1) /
        val32 s.mem B kEv 2 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have hn := h.old.workspace.nowrap
  unfold correction seqs
  refine WP.seq (WP.mono (correctionNumerator_ok h width fits) fun u ⟨hu, Ou, numerator, Ku⟩ => ?_)
  have h4 := correction_workspace hu.old
  have hz : 256 ≤ Z := h4.fits
  have E := correction_preserves_exponent Ou
  refine WP.seq (WP.mono (widenTo_ok hu .correction .exponent (.array .correction 2) (.fixed kEv)
    (by change 2 ≤ 4; decide) (by change 232 ≤ Z; omega) (by change 88 ≤ Z; omega) (Or.inl (by change 88 ≤ 208; decide))) fun v ⟨hv, Ov, fullDivisor, _, Kv⟩ => ?_)
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
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok (division_context (correction_workspace hv.old)))
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
  have changed : Outside B hdr 96 v.mem w.mem := division_frame Ow
  have hw := hv.keep Kw (changed.mono (Nat.zero_le _) (by unfold hdr; omega))
  have endSmall : arr 4 0 + 8 ≤ arr n aV := by unfold arr S aV hdr; omega
  refine WP.mono (widen_ok hw .exponent (VG.Impl.RsaKeyGen.X86.KeyRuntime.arr aV)
    (.array .correction 0) width (h.arr_fit (by decide))
    (by change 168 ≤ Z; omega) (Or.inl endSmall)) fun t ⟨ht, Ot, _, value, Kt⟩ => ?_
  have scratch : Outs B correctionScratch s.mem w.mem :=
    (Ou.trans (correction_scratch_arr (by decide) Ov)).trans
      (correction_scratch_outside (Nat.le_refl _) (Nat.le_refl _) changed)
  refine ⟨ht, ?_, value.trans quotientLow,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kw.trans (Kt.mono (by decide))))⟩
  exact (scratch.mono (fun r hr => List.mem_append_left _ hr)).trans
    (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/ExponentResultFrame.lean`, which only this module imported.
section

/-! # Result arithmetic preserves the already-computed inverse status -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponentTemps exponentArrays)

def exponentResultRanges (n : Nat) : List (Nat × Nat) :=
  (kProduct, 28) :: (hdr, 15 * S n) :: ranges n exponentArrays []

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
    exact Or.inr (Nat.le_trans (by decide : kProduct + 28 ≤ hdr) lower)
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
  · exact ⟨(kProduct, 28), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
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
  · exact ⟨(kProduct, 28), by simp [exponentResultRanges], Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨(hdr, 15 * S n), by simp [exponentResultRanges], ?_, ?_⟩
    · unfold arr
      omega
    · unfold arr S
      omega
  · exact ⟨(arr n aD, S n), by simp [exponentResultRanges, ranges, exponentArrays], Nat.le_refl _, by unfold S; omega⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/OddFinish.lean`, which only this module imported.
section

/-! # Finish the private exponent and recover the shared inverse result -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aD aDen aU aV kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (OddPrepared)

theorem dOddFinish_ok {s : State} {B : Addr} {Z n e L : Nat}
    (h : Ws s B Z n 32) (width : 2 ≤ n) (large : 3 ≤ e) (P : OddPrepared B n e L s) :
    WP isa dOddFinish s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentResultRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse e L = (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let x := num s.mem B 2 3
  have e64 : e < 2 ^ 64 := by rw [← P.exponent]; exact val32_lt _ _ _ _
  have Lbound : L < 2 ^ (32 * n) := by rw [← P.lcm]; exact val32_lt _ _ _ _
  have re : L % e < e := Nat.mod_lt _ (by omega)
  have QR : L = e * (L / e) + L % e := by
    have H := Nat.mod_add_div L e
    omega
  have Tbound : e - x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) e64
  unfold dOddFinish seqs
  refine WP.seq (WP.mono (complement_ok h width
    (by rw [P.exponent]; exact P.coefficient)) fun u ⟨hu, Ou, _, complement, Ku⟩ => ?_)
  rw [P.exponent] at complement
  change num u.mem B n aDen = e - x at complement
  have compFrame := exponent_result_complement Ou
  have Eu : val32 u.mem B kEv 2 = e := (exponent_result_header (by decide) compFrame).trans P.exponent
  have compKeep : Keep B n [aDen] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by omega) (by simp)
  have Qu : num u.mem B n aU = L / e :=
    (compKeep.num (by decide) (by simp) (h.fit64 (by decide))).trans P.quotient
  have Ru : num u.mem B n aV = L % e :=
    (compKeep.num (by decide) (by simp) (h.fit64 (by decide))).trans P.remainder
  have Rpair : val32 u.mem B (arr n aV) 2 = L % e :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num u.mem B n aV < 2 ^ 64; rw [Ru]; exact Nat.lt_trans re e64)).trans Ru
  have Tpair : val32 u.mem B (arr n aDen) 2 = e - x :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num u.mem B n aDen < 2 ^ 64; rw [complement]; exact Tbound)).trans complement
  refine WP.seq (WP.mono (correction_ok hu width (by rw [Eu]; omega)
    (by rw [Rpair, Tpair]; exact VG.Proof.RsaKeyGen.odd_numerator_fits e64 re)
    (by rw [Rpair, Tpair, Eu]; exact VG.Proof.RsaKeyGen.odd_correction_fits (by omega) e64 re))
    fun v ⟨hv, Ov, correction, Kv⟩ => ?_)
  rw [Rpair, Tpair, Eu] at correction
  have Qv : num v.mem B n aU = L / e :=
    (correction_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov).trans Qu
  have Tv : num v.mem B n aDen = e - x :=
    (correction_preserves_num (by decide) (by decide) (h.fit64 (by decide)) Ov).trans complement
  have TpairV : val32 v.mem B (arr n aDen) 2 = e - x :=
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq width (by change num v.mem B n aDen < 2 ^ 64; rw [Tv]; exact Tbound)).trans Tv
  have fits : num v.mem B n aU * val32 v.mem B (arr n aDen) 2 + num v.mem B n aV < 2 ^ (32 * n) := by
    rw [Qv, TpairV, correction]
    exact Nat.lt_of_le_of_lt (VG.Proof.RsaKeyGen.oddQuotient_le (by omega) QR) Lbound
  refine WP.mono (dProduct_ok hv width fits) fun t ⟨ht, Ot, product, Kt⟩ => ?_
  rw [Qv, TpairV, correction] at product
  have value : num t.mem B n aD = VG.Proof.RsaKeyGen.oddQuotient e (L / e) (L % e) x := product
  have frame := (compFrame.trans (exponent_result_correction Ov)).trans (exponent_result_product Ot)
  have mask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    rw [exponent_result_slot (by decide) frame, P.mask]
  refine ⟨ht, frame, ?_, ?_, (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  · rw [mask]
    split <;> omega
  · by_cases valid : 2 ≤ L ∧ Nat.gcd (L % e) e = 1
    · have congruence := P.congruence
      rw [valid.2] at congruence
      have inverse := VG.Proof.RsaKeyGen.oddQuotient_inverse large valid.1 QR congruence P.coefficient
      rw [mask, value]
      simpa only [valid, true_and, ite_true, Nat.one_ne_zero, ite_false] using inverse
    · have inverse := VG.Proof.RsaKeyGen.inverse_odd_none large QR valid
      rw [mask]
      simpa only [valid, ite_false, ite_true] using inverse

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DOdd.lean`, which only this module imported.
section

/-! # The native private exponent with a public odd exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aE aL aD aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges)

theorem dOdd_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dOdd s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dOdd
  refine WP.seq (WP.mono (dOddPrepare_ok h width large odd loaded one)
    fun u ⟨hu, Ou, P, Ku⟩ => ?_)
  refine WP.mono (dOddFinish_ok hu width large P) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  exact ⟨ht, Ou.trans (OutsS.of_outs (exponent_result_frame Ot)), bit, inverse, Ku.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DSelect.lean`, which only this module imported.
section

/-! # Select the specified private inverse using only the public exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aD aE aL aOne kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (exponentRanges exponent_keep_frame)

theorem dSelect_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa dSelect s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dSelect
  refine WP.seq (WP.mono (equalExponent_ok h 0) fun u ⟨hu, Mu, flag0, Ku⟩ => ?_)
  change isa.eval .e u = some (decide (val32 s.mem B kEv 2 = 0)) at flag0
  refine WP.ite _ flag0 (fun zero => ?_) (fun nonzero => ?_)
  · have E : val32 s.mem B kEv 2 = 0 := of_decide_eq_true zero
    refine WP.mono (dZero_ok hu) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
    refine ⟨ht, ?_, by rw [mask]; decide, ?_, (Ku.mono (by decide)).trans (Kt.mono (by decide))⟩
    · exact OutsS.of_outs (by simpa only [Mu] using exponent_keep_frame (by simp) (by decide) Ot)
    · rw [E, mask, VG.Proof.RsaKeyGen.inverse_zero]
      rfl
  · have E0 : val32 s.mem B kEv 2 ≠ 0 := of_decide_eq_false nonzero
    refine WP.seq (WP.mono (equalExponent_ok hu 1) fun v ⟨hv, Mv, flag1, Kv⟩ => ?_)
    have memoryV : v.mem = s.mem := Mv.trans Mu
    rw [Mu] at flag1
    change isa.eval .e v = some (decide (val32 s.mem B kEv 2 = 1)) at flag1
    refine WP.ite _ flag1 (fun unit => ?_) (fun nonunit => ?_)
    · have E : val32 s.mem B kEv 2 = 1 := of_decide_eq_true unit
      refine WP.mono (dOne_ok hv (by rw [memoryV]; exact one)) fun t ⟨ht, Ot, D, mask, Kt⟩ => ?_
      rw [memoryV] at mask
      refine ⟨ht, ?_, ?_, ?_, (Ku.mono (by decide)).trans
        ((Kv.mono (by decide)).trans (Kt.mono (by decide)))⟩
      · exact OutsS.of_outs (by simpa only [memoryV] using exponent_keep_frame (by decide) (by decide) Ot)
      · rw [mask]
        split <;> decide
      · rw [E, VG.Proof.RsaKeyGen.inverse_one, mask, D]
        by_cases L : num s.mem B n aL = 1 <;> simp [L]
    · have E1 : val32 s.mem B kEv 2 ≠ 1 := of_decide_eq_false nonunit
      refine WP.seq (WP.mono (parityExponent_ok hv) fun w ⟨hw, Mw, parity, Kw⟩ => ?_)
      have memoryW : w.mem = s.mem := Mw.trans memoryV
      rw [memoryV] at parity
      refine WP.ite _ parity (fun even => ?_) (fun odd => ?_)
      · refine WP.mono (dEven_ok hw (by rw [memoryW]; exact of_decide_eq_true even)
          (by rw [memoryW]; exact loaded)) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
        have spW : w.gpr .esp = s.gpr .esp := by
          rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
        rw [memoryW, spW] at Ot
        rw [memoryW] at inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩
      · have O : val32 s.mem B kEv 2 % 2 = 1 := by
          have H := of_decide_eq_false odd
          omega
        refine WP.mono (dOdd_ok hw width (by rw [memoryW]; omega)
          (by rw [memoryW]; exact O) (by rw [memoryW]; exact loaded)
          (by rw [memoryW]; exact one)) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
        have spW : w.gpr .esp = s.gpr .esp := by
          rw [Kw.1 .esp (by decide), Kv.1 .esp (by decide), Ku.1 .esp (by decide)]
        rw [memoryW, spW] at Ot
        rw [memoryW] at inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aPm aQm aE aOne kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady prepareArrays stageRanges stage_keep stage_preserves_num
  stage_mono stage_preserves_e exponentArrays exponent_preserves_num)

theorem prepareLoaded_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa prepareLoaded s fun t =>
      Ws t B Z n 32 ∧ OutsS B (s.gpr .esp) (stageRanges n prepareArrays) s.mem t.mem ∧
      KeyReady B n (val32 s.mem B kEv 2) (num s.mem B n aPa) (num s.mem B n aQa) t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have small : k ≤ n := by omega
  have wide : 2 ≤ n := by omega
  have pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  unfold prepareLoaded seqs
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, P, Q, Pm, Qm, product, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  have frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.seq (WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun v ⟨hv, Ov, L, Kv⟩ => ?_)
  rw [Pm, Qm] at L
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have spV : v.gpr .esp = s.gpr .esp := by rw [Kv.1 .esp (by decide), spU]
  have narrowFrame := OutsS.lift (fun _ _ => lcm_stage_frame small) Ov
  have Pv : num v.mem B n aPa = max (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans P
  have Qv : num v.mem B n aQa = min (num s.mem B n aPa) (num s.mem B n aQa) :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Q
  have Pmv : num v.mem B n aPm = max (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pm
  have Qmv : num v.mem B n aQm = min (num s.mem B n aPa) (num s.mem B n aQa) - 1 :=
    (hu.read_num (by decide) narrowFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qm
  have frameV : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) u.mem v.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ => stage_mono (by decide)) narrowFrame
  have prefixFrame := (OutsS.of_outs frameU).trans frameV
  have E : val32 v.mem B kEv 2 = val32 s.mem B kEv 2 := h.read_val32 (by decide) prefixFrame stage_preserves_e
  have loadedV : num v.mem B n aE = val32 v.mem B kEv 2 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans (loaded.trans E.symm)
  have oneV : num v.mem B n aOne = 1 :=
    (h.read_num (by decide) prefixFrame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one
  refine WP.mono (dSelect_ok hv wide loadedV oneV) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  rw [E, L] at inverse
  have frameT : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) v.mem t.mem := by
    rw [← spV]
    exact OutsS.lift (fun _ _ => stage_mono (js := exponentArrays) (by decide)) Ot
  have frame := prefixFrame.trans frameT
  refine ⟨ht, frame, ⟨?_, ?_, ?_, ?_, ?_, h.read_val32 (by decide) frame stage_preserves_e, ?_, ?_, inverse, bit⟩,
    (Ku.mono (by decide)).trans (Kv.trans Kt)⟩
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Pmv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans Qmv
  · exact (hv.read_num (by decide) Ot (exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans L
  · exact (h.read_num (by decide) frame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans loaded
  · exact (h.read_num (by decide) frame (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))).trans one

end VG.Proof.RsaKeyGen.X86.KeyRuntime
