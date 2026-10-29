module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepareFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdIsOne
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBorrowMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
/-! # Prepare the private exponent using only a two-word inverse -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyLAtLeastTwo.lean`, which only this module imported.
section

/-! # The public-exponent inverse also needs an LCM of at least two -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem lAtLeastTwo_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kFlag ≤ 1) :
    WP isa (lAtLeastTwo n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 2 ≤ num s.mem B n aL ∧ slot s.mem B kFlag = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have bound : 2 < 2 ^ (32 * n) := by
    have P : 2 ^ 2 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega)
    omega
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold lAtLeastTwo seqs
  refine WP.seq (WP.mono (constArray_ok h (by decide) bound) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have L : num u.mem B n aL = num s.mem B n aL := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub3_ok hu (by decide) (by decide) (by decide) (by decide) (by decide))
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

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dOddPrepare_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa (dOddPrepare n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentRanges n) s.mem t.mem ∧
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
  have h2 := inverse_workspace hu (by decide : 0 < 2) width
  have layout : InverseLayout Z 2 (arr n aV) kEv := by
    have fit := hu.arr_fit (j := aV) (by decide)
    have head := hu.hdr_le
    refine ⟨?_, ?_, Or.inr (inverse_end_le width (by decide)), Or.inl (by decide)⟩
    · unfold S at fit
      omega
    · unfold kEv hdr at *
      omega
  refine WP.seq (WP.mono (inverseFrom_ok h2 layout
    (by rw [Eu]; exact eo) (by rw [Eu]; omega)) fun v ⟨hv2, Ov, gcd, congruence, boundX, Kv⟩ => ?_)
  change num v.mem B 2 1 = Nat.gcd (val32 u.mem B (arr n aV) 2) (val32 u.mem B kEv 2) at gcd
  change (val32 u.mem B kEv 2 : Int) ∣ (num v.mem B 2 3 : Int) * val32 u.mem B (arr n aV) 2 - num v.mem B 2 1 at congruence
  rw [remainderLow, Eu] at gcd congruence
  rw [gcd] at congruence
  rw [Eu] at boundX
  have inverseFrame := exponent_temps_inverse width Ov
  have hv := hu.rest Kv
  refine WP.seq (WP.mono (gcdIsOne_ok hv2 (Nat.le_refl _)) fun w ⟨_, Ow, flag, Kw⟩ => ?_)
  rw [gcd] at flag
  have coefficientW : num w.mem B 2 3 = num v.mem B 2 3 :=
    Ow.num (by decide) (by decide) (hv2.fit64 (by decide))
  have compareFrame : Outs B (exponentTemps n) v.mem w.mem :=
    exponent_temps_keep width (by decide) (by decide) Ow
  have prefixFrame : Outs B (exponentRanges n) s.mem w.mem :=
    divisionFrame.trans ((inverseFrame.trans compareFrame).mono (fun r hr => List.mem_append_left _ hr))
  have Lw : num w.mem B n aL = L :=
    exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) prefixFrame
  have bit : slot w.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  have hw := hv.rest Kw
  refine WP.mono (lAtLeastTwo_ok hw bit) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  have maskFrame : Outs B (exponentTemps n) w.mem t.mem :=
    exponent_temps_keep (Nat.le_refl n) (by decide) (by decide) Ot
  have tailFrame := (inverseFrame.trans compareFrame).trans maskFrame
  have frame : Outs B (exponentRanges n) s.mem t.mem :=
    divisionFrame.trans (tailFrame.mono (fun r hr => List.mem_append_left _ hr))
  have coefficientT : num t.mem B 2 3 = num v.mem B 2 3 :=
    (exponent_mask_coefficient Ot).trans coefficientW
  have finalMask : slot t.mem B kOk = (if 2 ≤ L ∧ Nat.gcd (L % e) e = 1 then 1 else 0) := by
    by_cases G : Nat.gcd (L % e) e = 1 <;> simpa [Lw, flag, G] using mask
  refine ⟨ht, frame, ⟨exponent_preserves_e frame, ?_, ?_, ?_, ?_, ?_, ?_, finalMask⟩,
    Ku.trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · exact exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) frame
  · exact (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)) tailFrame).trans Q
  · exact (exponent_temps_preserves_num (by decide) (h.fit64 (by decide)) tailFrame).trans R
  · rw [exponent_preserves_num (by decide) (by decide) (h.fit64 (by decide)) frame, one]
  · rw [coefficientT]
    exact boundX
  · rw [coefficientT]
    exact congruence

end VG.Proof.RsaKeyGen.X86.Key
