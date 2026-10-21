module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPartResult

/-! # The native post-retry arithmetic produces the shared key or failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem KeyReady.part {s t : State} {B : Addr} {Z n e p q : Nat}
    (h : Ws s B Z n 32) (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : p < 2 ^ (16 * n)) (boundQ : q < 2 ^ (16 * n))
    (R : KeyReady B n e p q s.mem)
    (notSmall : ¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)))
    (F : Outs B (stageRanges n keyPartArrays) s.mem t.mem) (K : KeyPartResult B n s.mem t) :
    CoreOutcome B n e p q t.mem := by
  have boundE : e < 2 ^ 64 := by rw [← R.exponent]; exact val32_lt _ _ _ _
  have congruence := K.qiCongruence
  have boundX := K.qiBound
  rw [R.pValue, R.qValue] at congruence
  rw [R.pValue] at boundX
  have code := keyFromPrimes_native lower upper boundP boundQ boundE congruence boundX
  have mask := K.mask
  rw [R.pValue, R.qValue, R.exponent] at mask
  unfold CoreOutcome
  rw [code]
  by_cases empty : slot s.mem B kOk = 0
  · have inverse := R.inverse
    rw [empty, ite_eq_left rfl] at inverse
    rw [inverse]
    dsimp only
    have M : slot t.mem B kOk = 0 := by simpa only [empty, Nat.zero_ne_one, false_and, ite_false] using mask
    exact ⟨K.status.trans M, M⟩
  · have unit : slot s.mem B kOk = 1 := by have H := R.bit; omega
    have inverse := R.inverse
    rw [unit, ite_eq_right (by decide : ¬(1 : Nat) = 0)] at inverse
    have large : ¬num s.mem B n aD ≤ 2 ^ (16 * n) := fun small => notSmall ⟨unit, small⟩
    rw [inverse]
    dsimp only
    rw [ite_eq_right large]
    have M : slot t.mem B kOk = if nativeShape n e (max p q) (min p q) then 1 else 0 := by
      rw [unit] at mask
      simpa only [nativeShape, true_and, and_assoc, and_comm, and_left_comm] using mask
    by_cases shape : nativeShape n e (max p q) (min p q)
    · rw [ite_eq_left shape]
      have accepted : slot t.mem B kOk = 1 := by rw [M, ite_eq_left shape]
      refine ⟨K.status.trans accepted, accepted, ?_⟩
      have two : 2 ≤ 2 ^ (16 * n) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 16 * n)
      have factors := VG.Proof.RsaKeyGen.primes_of_inverse
        (Nat.le_trans (Nat.min_le_left p q) (Nat.le_max_left p q)) inverse (by omega)
      have Pm : max p q - 1 ≠ 0 := by omega
      have Qm : min p q - 1 ≠ 0 := by omega
      have pFinal : num t.mem B n aPa = max p q :=
        (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) F).trans R.pValue
      have qFinal : num t.mem B n aQa = min p q :=
        (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) F).trans R.qValue
      have dFinal : num t.mem B n aD = num s.mem B n aD :=
        stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)) F
      have eFinal : val32 t.mem B kEv 2 = e := (stage_preserves_e F).trans R.exponent
      have dp := K.dp
      have dq := K.dq
      rw [R.pm, crtDivisor, ite_eq_right Pm] at dp
      rw [R.qm, crtDivisor, ite_eq_right Qm] at dq
      unfold assembledKey
      rw [K.modulus, R.pValue, R.qValue, pFinal, qFinal, dFinal, eFinal, dp, dq]
    · rw [ite_eq_right shape]
      have rejected : slot t.mem B kOk = 0 := by rw [M, ite_eq_right shape]
      exact ⟨K.status.trans rejected, rejected⟩

end VG.Proof.RsaKeyGen.X86.Key
