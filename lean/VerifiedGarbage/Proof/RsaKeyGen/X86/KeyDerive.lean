module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyQinv
public import VerifiedGarbage.Spec.Rsa
public import Init.Data.Nat.Coprime
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEvenFrame
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import Aesop.BuiltinRules

/-! ### `RsaKeyGen.X86.KeyPartOutcome`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyPartResult`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCrtCorrect`, which this module and modules that import it used -/

section

/-! # Compute both CRT exponents with safe fixed-schedule division -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def crtArrays : List Nat := [aDen, aU, aDp, aDq]
def crtDivisor (x : Nat) : Nat := if x = 0 then 1 else x

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The computed key components before masked external export -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def keyPartArrays : List Nat := [aDen, aQi, aU, aDp, aDq, aN]

structure KeyPartResult (B : Addr) (n : Nat) (m : Mem) (t : State) : Prop where
  modulus : num t.mem B n aN = num m B n aPa * num m B n aQa
  dp : num t.mem B n aDp = num m B n aD % crtDivisor (num m B n aPm)
  dq : num t.mem B n aDq = num m B n aD % crtDivisor (num m B n aQm)
  qiBound : num t.mem B n aQi < safePrime (num m B n aPa)
  qiCongruence : (safePrime (num m B n aPa) : Int) ∣
    (num t.mem B n aQi : Int) * num m B n aQa - Nat.gcd (num m B n aQa) (safePrime (num m B n aPa))
  mask : slot t.mem B kOk = (if slot m B kOk = 1 ∧
    Nat.gcd (num m B n aQa) (safePrime (num m B n aPa)) = 1 ∧
    2 ^ (32 * n - 1) ≤ num m B n aPa * num m B n aQa ∧
    num m B n aPa % 2 = 1 ∧ num m B n aQa % 2 = 1 ∧
    Spec.Rsa.exponentValid (val32 m B kEv 2) = true then 1 else 0)
  status : slot t.mem B kStatus = slot t.mem B kOk

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The native post-retry arithmetic produces the shared key or failure -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

/-- The key part's outcome (`CoreOutcome`), from what it leaves of the factors, `d` and `e`. -/
theorem KeyReady.part_of {s t : State} {B : Addr} {n e p q : Nat}
    (lower : 16 ≤ n) (upper : n ≤ 256)
    (boundP : p < 2 ^ (16 * n)) (boundQ : q < 2 ^ (16 * n))
    (R : KeyReady B n e p q s.mem)
    (notSmall : ¬(slot s.mem B kOk = 1 ∧ num s.mem B n aD ≤ 2 ^ (16 * n)))
    (keptP : num t.mem B n aPa = num s.mem B n aPa) (keptQ : num t.mem B n aQa = num s.mem B n aQa)
    (keptD : num t.mem B n aD = num s.mem B n aD) (keptE : val32 t.mem B kEv 2 = val32 s.mem B kEv 2)
    (K : KeyPartResult B n s.mem t) :
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
  · have unit : slot s.mem B kOk = 1 := by have H := R.bit; omega_using [empty, H]
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
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega_using [lower] : 1 ≤ 16 * n)
      have factors := VG.Proof.RsaKeyGen.primes_of_inverse
        (Nat.le_trans (Nat.min_le_left p q) (Nat.le_max_left p q)) inverse (by omega_using [boundP, notSmall, unit])
      have Pm : max p q - 1 ≠ 0 := by omega_using [factors]
      have Qm : min p q - 1 ≠ 0 := by omega_using [factors]
      have pFinal : num t.mem B n aPa = max p q := keptP.trans R.pValue
      have qFinal : num t.mem B n aQa = min p q := keptQ.trans R.qValue
      have dFinal : num t.mem B n aD = num s.mem B n aD := keptD
      have eFinal : val32 t.mem B kEv 2 = e := keptE.trans R.exponent
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

end

end

/-! # Complete native numeric RSA derivation, including all failure cases -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def deriveArrays : List Nat := prepareArrays ++ keyPartArrays

end VG.Proof.RsaKeyGen.X86.Key
