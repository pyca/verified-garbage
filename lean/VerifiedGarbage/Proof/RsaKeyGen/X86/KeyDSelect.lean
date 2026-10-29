module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDTrivial
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddFinish
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepareFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddModulus
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaveSlot
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdIsOne
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
/-! # Select the specified private inverse using only the public exponent -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDOdd.lean`, which only this module imported.
section

/-! # The native private exponent with a public odd exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem dOdd_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa (dOdd n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dOdd
  refine WP.seq (WP.mono (dOddPrepare_ok h width large odd loaded one)
    fun u ⟨hu, Ou, P, Ku⟩ => ?_)
  refine WP.mono (dOddFinish_ok hu width large P) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  exact ⟨ht, Ou.trans (exponent_result_frame Ot), bit, inverse, Ku.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDEven.lean`, which only this module imported.
section

/-! # A modulus-width fallback for public even exponents -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem dEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (even : val32 s.mem B kEv 2 % 2 = 0)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) :
    WP isa (dEven n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let e := val32 s.mem B kEv 2
  let L := num s.mem B n aL
  let valid := L % 2 = 1 ∧ 3 ≤ L
  let M := if valid then L else 3
  have eo : e % 2 = 0 := even
  have mo : M % 2 = 1 := by
    unfold M
    split
    · next H => exact H.1
    · decide
  have ml : 1 < M := by unfold M; split <;> omega
  unfold dEven seqs
  refine WP.seq (WP.mono (oddModulus_ok h (by decide) (by decide) (by decide))
    fun u ⟨hu, Ou, flag, modulus, Ku⟩ => ?_)
  change num u.mem B n aDen = M at modulus
  change slot u.mem B kFlag = (if valid then 1 else 0) at flag
  have Eu : num u.mem B n aE = e :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans loaded
  have frameU := exponent_keep_frame (by decide) (by decide) Ou
  refine WP.seq (WP.mono (saveSlot_ok hu (by decide) (by decide))
    fun v ⟨hv, Ov, saved, Kv⟩ => ?_)
  have maskV : slot v.mem B kOk = (if valid then 1 else 0) := saved.trans flag
  have Mv : num v.mem B n aDen = M :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans modulus
  have Ev : num v.mem B n aE = e :=
    (Ov.num (by simp) (by decide) (h.fit64 (by decide))).trans Eu
  have frameV := exponent_keep_frame (by decide) (by decide) Ov
  refine WP.seq (WP.mono (arrayDivision_ok hv (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [Mv]; omega))
    fun w ⟨hw, Ow, _, R, Kw⟩ => ?_)
  rw [Ev, Mv] at R
  have Mw : num w.mem B n aDen = M :=
    (arrayDivision_preserves_num (by decide) (by decide) (by decide) (h.fit64 (by decide)) Ow).trans Mv
  have maskW : slot w.mem B kOk = (if valid then 1 else 0) :=
    (arrayDivision_preserves_slot (by decide) Ow).trans maskV
  have frameW := exponent_division_frame Ow
  have hi := inverse_workspace hw hw.wpos (Nat.le_refl n)
  have layout := inverse_array_layout hw (Nat.le_refl n) (by decide : aV < 32)
    (by decide : aDen < 32) (by decide) (by decide)
  refine WP.seq (WP.mono (inverseFrom_ok hi layout (by change num w.mem B n aDen % 2 = 1; rw [Mw]; exact mo)
    (by change 1 < num w.mem B n aDen; rw [Mw]; exact ml))
    fun a ⟨_, Oa, gcd, congruence, boundX, Ka⟩ => ?_)
  change num a.mem B n 1 = Nat.gcd (num w.mem B n aV) (num w.mem B n aDen) at gcd
  change (num w.mem B n aDen : Int) ∣ (num a.mem B n 3 : Int) * num w.mem B n aV - num a.mem B n 1 at congruence
  change num a.mem B n 3 < num w.mem B n aDen at boundX
  rw [R, Mw] at gcd congruence
  rw [Mw] at boundX
  rw [gcd] at congruence
  have ha := hw.rest Ka
  have maskA : slot a.mem B kOk = (if valid then 1 else 0) :=
    (inverse_preserves_slot (by decide) Oa).trans maskW
  have frameA : Outs B (exponentRanges n) w.mem a.mem :=
    (exponent_temps_inverse (Nat.le_refl n) Oa).mono (fun r hr => List.mem_append_left _ hr)
  refine WP.seq (WP.mono (gcdIsOne_ok ha (by decide)) fun b ⟨hb, Ob, flagB, Kb⟩ => ?_)
  rw [gcd] at flagB
  have maskB : slot b.mem B kOk = (if valid then 1 else 0) :=
    (Ob.slot (by decide) (by decide)).trans maskA
  have Xb : num b.mem B n 3 = num a.mem B n 3 :=
    Ob.num (by decide) (by decide) (h.fit64 (by decide))
  have frameB := exponent_keep_frame (by decide) (by decide) Ob
  refine WP.seq (WP.mono (andS_ok hb (by decide) (by decide) (by decide)
    (by rw [maskB]; split <;> omega) (by rw [flagB]; split <;> omega))
    fun c ⟨hc, Oc, maskC, Kc⟩ => ?_)
  rw [maskB, flagB] at maskC
  have Xc : num c.mem B n 3 = num a.mem B n 3 :=
    (Oc.num (by simp) (by decide) (h.fit64 (by decide))).trans Xb
  have frameC := exponent_keep_frame (by decide) (by decide) Oc
  refine WP.mono (copy_ok hc (by decide) (by decide)) fun t ⟨ht, Ot, copied, Kt, _⟩ => ?_
  rw [Xc] at copied
  have maskT : slot t.mem B kOk =
      (if (if valid then 1 else 0) = 1 ∧ (if Nat.gcd (e % M) M = 1 then 1 else 0) = 1 then 1 else 0) :=
    (Ot.slot (by decide) (by simp)).trans maskC
  have frameT := exponent_keep_frame (by decide) (by simp) Ot
  refine ⟨ht, (((((frameU.trans frameV).trans frameW).trans frameA).trans frameB).trans frameC).trans frameT,
    ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans
      (Kw.trans (Ka.trans ((Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kt.mono (by decide)))))))⟩
  · rw [maskT]
    by_cases V : valid <;> by_cases G : Nat.gcd (e % M) M = 1 <;> simp [V, G]
  · change Spec.Rsa.inverse e L = _
    by_cases V : valid
    · have ME : M = L := ite_eq_left V
      have V' : L % 2 = 1 ∧ 3 ≤ L := V
      by_cases G : Nat.gcd (e % M) M = 1
      · have C : (L : Int) ∣ (num a.mem B n 3 : Int) * (e % L) - 1 := by
          rw [G, ME] at congruence
          exact congruence
        have I := VG.Proof.RsaKeyGen.inverse_even V'.2 C (by simpa only [ME] using boundX)
        simpa only [maskT, V, G, ite_true, true_and, Nat.one_ne_zero, ite_false, copied] using I
      · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
          intro H; exact G (by simpa only [ME] using H.2.2))
        simpa only [maskT, V, G, ite_true, ite_false, Nat.zero_ne_one, and_false, ↓reduceIte] using I
    · have I := VG.Proof.RsaKeyGen.inverse_even_none eo (by
        intro H; exact V ⟨H.1, H.2.1⟩)
      simpa only [maskT, V, ite_false, Nat.zero_ne_one, false_and, ↓reduceIte] using I

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem dSelect_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa (dSelect n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
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
    · simpa only [Mu] using exponent_keep_frame (by simp) (by decide) Ot
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
      · simpa only [memoryV] using exponent_keep_frame (by decide) (by decide) Ot
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
        rw [memoryW] at Ot inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩
      · have O : val32 s.mem B kEv 2 % 2 = 1 := by
          have H := of_decide_eq_false odd
          omega
        refine WP.mono (dOdd_ok hw width (by rw [memoryW]; omega)
          (by rw [memoryW]; exact O) (by rw [memoryW]; exact loaded)
          (by rw [memoryW]; exact one)) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
        rw [memoryW] at Ot inverse
        exact ⟨ht, Ot, bit, inverse, (Ku.mono (by decide)).trans
          ((Kv.mono (by decide)).trans ((Kw.mono (by decide)).trans Kt))⟩

end VG.Proof.RsaKeyGen.X86.Key
