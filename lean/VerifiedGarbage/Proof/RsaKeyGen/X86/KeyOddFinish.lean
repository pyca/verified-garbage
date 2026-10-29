module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentResultFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
/-! # Finish the private exponent and recover the shared inverse result -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPairSubtract.lean`, which only this module imported.
section

/-! # Paired native subtraction for the private-exponent complement -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key

theorem subtractPair_ok {s : State} {B : Addr} {Z out a b : Nat} (h : Scr s B Z)
    (fa : a + 8 ≤ Z) (fb : b + 8 ≤ Z) (fo : out + 8 ≤ Z) :
    WP isa (.block (subtractPair out a b)) s fun t =>
      Outside B out 8 s.mem t.mem ∧
      (∃ borrow : Bool, val32 t.mem B out 2 + val32 s.mem B b 2 =
        val32 s.mem B a 2 + 2 ^ 64 * borrow.toNat) ∧ Keeps [.eax, .edx] s t := by
  have hn := h.nowrap
  unfold subtractPair
  refine wp_movS (readSrc_sc h (by omega_arith)) fun u U _ => ?_
  have hu := h.of_keeps U.keeps (by decide)
  refine wp_movS (readSrc_sc hu (by omega_arith)) fun v V _ => ?_
  have Kv : Keeps [.eax, .edx] s v := (U.keeps.mono (by decide)).widen V.keeps
  have hv := h.of_keeps Kv (by decide)
  have loRead := readSrc_sc hv (d := b) (by omega_arith)
  rw [V.mem, U.mem] at loRead
  refine wp_subS loRead fun w W cfW => ?_
  have Kw : Keeps [.eax, .edx] s w := Kv.widen W.keeps
  have hw := h.of_keeps Kw (by decide)
  have hiRead := readSrc_sc hw (d := b + 4) (by omega_arith)
  rw [W.mem, V.mem, U.mem] at hiRead
  refine wp_sbbS hiRead cfW fun x X _ => ?_
  have Kx : Keeps [.eax, .edx] s x := Kw.widen X.keeps
  have hx := h.of_keeps Kx (by decide)
  refine wp_storeS (hx.ea (by omega_arith)) (hx.write (by omega_arith)) fun y Y => ?_
  have hy := hx.of_keeps (Y.keeps []) (by decide)
  refine wp_storeS (hy.ea (by omega_arith)) (hy.write (by omega_arith)) fun t T => WP.block_nil ?_
  let lowBorrow := decide ((v.gpr .eax).toNat < (s.mem.readW (off B b) 32).toNat)
  let highBorrow := decide ((w.gpr .edx).toNat < (s.mem.readW (off B (b + 4)) 32).toNat + lowBorrow.toNat)
  have low : (w.gpr .eax).toNat + w32 s.mem B b = (v.gpr .eax).toNat + 2 ^ 32 * lowBorrow.toNat := by
    rw [W.gpr]
    have H := sbb_rel (v.gpr .eax) (s.mem.readW (off B b) 32) false
    simpa only [show (BitVec.ofBool false).setWidth 32 = 0#32 from rfl, BitVec.sub_zero,
      Bool.toNat_false, Nat.add_zero] using H
  have high : (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
      (w.gpr .edx).toNat + 2 ^ 32 * highBorrow.toNat := by rw [X.gpr]; exact sbb_rel ..
  rw [V.other _ (by decide), U.gpr] at low
  rw [W.other _ (by decide), V.gpr, U.mem] at high
  change (w.gpr .eax).toNat + w32 s.mem B b = w32 s.mem B a + 2 ^ 32 * lowBorrow.toNat at low
  change (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
    w32 s.mem B (a + 4) + 2 ^ 32 * highBorrow.toNat at high
  have oldMem : x.mem = s.mem := X.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have Oy : Outside B out 4 s.mem y.mem := by
    rw [Y.mem, oldMem]
    exact writeW32_outside _ _ _ (by omega_arith)
  have Ot : Outside B (out + 4) 4 y.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by omega_arith)
  have lowT : w32 t.mem B out = (x.gpr .eax).toNat := by
    rw [Ot.w32 (Or.inl (Nat.le_refl _)) (by omega_arith), Y.mem, w32_write_self]
  have highT : w32 t.mem B (out + 4) = (x.gpr .edx).toNat := by
    rw [T.mem, w32_write_self, Y.gpr]
  refine ⟨(Oy.mono (Nat.le_refl _) (by omega_arith)).trans (Ot.mono (by omega_arith) (by omega_arith)),
    ⟨highBorrow, ?_⟩, Kx.trans ((Y.keeps _).trans (T.keeps _))⟩
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [lowT, highT, X.other _ (by decide)]
  omega_arith

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyComplement.lean`, which only this module imported.
section

/-! # Form the public-exponent complement from the tiny inverse coefficient -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem complement_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (less : val32 s.mem B (arr 2 3) 2 < val32 s.mem B kEv 2) :
    WP isa (complement n) s fun t =>
      Ws t B Z n 32 ∧ Outside B (arr n aDen) (S n) s.mem t.mem ∧
      val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      num t.mem B n aDen = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fit := h.arr_fit (j := aDen) (by decide)
  have fits := h.fits
  have hn := h.workspace.nowrap
  have eBound : kEv + 8 ≤ Z := by have := h.hdr_le; unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega_arith
  have xBound : arr 2 3 + 8 ≤ Z := by unfold arr S VG.Impl.Rsa.X86.Keys.hdr at fits ⊢; omega_arith
  have beforeE : kEv + 8 ≤ arr n aDen := by unfold arr S kEv aDen VG.Impl.Rsa.X86.Keys.hdr; omega_arith
  have beforeX : arr 2 3 + 8 ≤ arr n aDen := by unfold arr S aDen VG.Impl.Rsa.X86.Keys.hdr; omega_arith
  unfold complement
  refine WP.seq (WP.mono (zerosW_ok h.workspace (by omega_arith)
    (by change arr n aDen + 4 * (n + 2) ≤ Z; exact fit)) fun u ⟨Ou, zero, Ku⟩ => ?_)
  change Outside B (arr n aDen) (4 * (n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (arr n aDen) (n + 2) = 0 at zero
  have hu := h.rest Ku
  have E : val32 u.mem B kEv 2 = val32 s.mem B kEv 2 := Ou.val32 (Or.inl beforeE) (by omega_arith)
  have X : val32 u.mem B (arr 2 3) 2 = val32 s.mem B (arr 2 3) 2 := Ou.val32 (Or.inl beforeX) (by omega_arith)
  refine WP.mono (subtractPair_ok hu.workspace eBound xBound
    (by change arr n aDen + 8 ≤ Z; unfold S at fit; omega_arith)) fun t ⟨Ot, ⟨borrow, value⟩, Kt⟩ => ?_
  change Outside B (arr n aDen) 8 u.mem t.mem at Ot
  change val32 t.mem B (arr n aDen) 2 + val32 u.mem B (arr 2 3) 2 =
    val32 u.mem B kEv 2 + 2 ^ 64 * borrow.toNat at value
  rw [E, X] at value
  have noBorrow := (VG.Proof.Rsa.borrow_iff value (val32_lt t.mem B (arr n aDen) 2) (Bool.toNat_le borrow)).mpr
    (Nat.le_of_lt less)
  rw [noBorrow, Nat.mul_zero, Nat.add_zero] at value
  have result : val32 t.mem B (arr n aDen) 2 = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by omega_arith
  have high : val32 u.mem B (arr n aDen + 8) n = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 2) (c := n) (by omega_arith)
  have highT : val32 t.mem B (arr n aDen + 8) n = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by unfold S at fit; omega_arith), high]
  have full : val32 t.mem B (arr n aDen) (n + 2) = val32 s.mem B kEv 2 - val32 s.mem B (arr 2 3) 2 := by
    rw [show n + 2 = 2 + n by omega_arith, val32_append, highT, Nat.mul_zero, Nat.add_zero, result]
  have bound : val32 t.mem B (arr n aDen) (n + 2) < 2 ^ (32 * n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (val32_lt s.mem B kEv 2))
      (Nat.pow_le_pow_right (by decide) (by omega_arith))
  exact ⟨hu.rest Kt, Ou.trans (Ot.mono (Nat.le_refl _) (by omega_arith)), full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_arith : n ≤ n + 2) bound).trans full,
    Ku.trans (Kt.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

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
