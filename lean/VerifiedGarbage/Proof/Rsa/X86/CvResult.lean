module

public import VerifiedGarbage.Proof.Rsa.X86.CvSized
import VerifiedGarbage.Proof.Rsa.CrtValuesMath
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The calculated and masked CRT outputs satisfy the shared RSA result definition -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86

def outputBuffers (g : CallGeometry) : List (Addr × Nat) :=
  [((g.buffer 0).base, (g.buffer 0).len), ((g.buffer 2).base, (g.buffer 2).len), ((g.buffer 4).base, (g.buffer 4).len)]

def calculated (g : CallGeometry) (m : Mem) :=
  Spec.Rsa.crtKey (inputBytes g m 0) (inputBytes g m 1) (inputBytes g m 2) (inputBytes g m 3)

def Written (g : CallGeometry) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.writtenAll t.mem (outputBuffers g) (t.gpr .eax)
    ((calculated g m).map fun v => [v.1, v.2.1, v.2.2])

theorem written_arithmetic {g : CallGeometry} {m : Mem} {t : State} (h : ArithmeticPost g m t)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g m 0)) (inputBytes g m 0).length = true)
    (pl : (inputBytes g m 1).length < (inputBytes g m 0).length)
    (ql : (inputBytes g m 2).length < (inputBytes g m 0).length)
    (dpLen : (g.buffer 0).len = (inputBytes g m 1).length)
    (dqLen : (g.buffer 2).len = (inputBytes g m 2).length)
    (qiLen : (g.buffer 4).len = (inputBytes g m 1).length) : Written g m t := by
  obtain ⟨X₁, X₂, V, R₂, R₃, X, division, inverse, remP, remQ, dp, dq, qi, status⟩ := h
  dsimp only [arithmeticGeometry, Geometry.M] at division inverse remP remQ dp dq qi status
  have key := VG.Proof.Rsa.CrtValues.crtKey_masked valid pl ql division inverse remP remQ
  unfold Written calculated
  rw [key]
  dsimp only [maskOf] at dp dq qi status
  generalize hc : VG.Proof.Rsa.CrtValues.maskOf (Spec.Rsa.os2ip (inputBytes g m 1))
    (Spec.Rsa.os2ip (inputBytes g m 2)) X₁ X₂ V = c at *
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Option.map_none] at *
    simp only [encode, Bool.false_eq_true, ite_false, Nat.zero_mod, i2osp_zero'] at dp dq qi
    refine ⟨status, ?_⟩
    simp only [outputBuffers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨dp, dq, qi⟩
  | true =>
    simp only [ite_true, Option.map_some] at *
    refine ⟨status, ?_⟩
    simp only [outputBuffers, List.map_cons, List.map_nil]
    simp only [encode, ite_true] at dp dq qi
    rw [dp, dq, qi]
    change (g.buffer (2 * (0 : Fin 3).val)).len = _ at dpLen
    change (g.buffer (2 * (1 : Fin 3).val)).len = _ at dqLen
    change (g.buffer (2 * (2 : Fin 3).val)).len = _ at qiLen
    rw [dpLen, dqLen, qiLen]
end VG.Proof.Rsa.X86.CrtValues
