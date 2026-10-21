module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDTrivial
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDOdd
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDEven
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath

/-! # Select the specified private inverse using only the public exponent -/

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
