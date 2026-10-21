module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentResultFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyComplement
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32

/-! # Finish the private exponent and recover the shared inverse result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dOddFinish_ok {s : State} {B : Addr} {Z n e L : Nat}
    (h : Ws s B Z n 32) (width : 2 ≤ n) (large : 3 ≤ e) (P : OddPrepared B n e L s) :
    WP isa (dOddFinish n) s fun t =>
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

end VG.Proof.RsaKeyGen.X86.Key
