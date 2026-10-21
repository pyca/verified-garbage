module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
import VerifiedGarbage.Proof.RsaKeyGen.Retry

/-! # The secret native retry comparison equals the released shared result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem KeyReady.retry_iff {B : Addr} {n e p q : Nat} {m : Mem} (R : KeyReady B n e p q m) :
    (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n)) ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr () := by
  rw [VG.Proof.RsaKeyGen.keyFromPrimes_retry_iff, show 32 * n / 2 = 16 * n by omega, R.inverse]
  by_cases zero : slot m B kOk = 0
  · simp only [zero, ite_true, reduceCtorEq, false_and, exists_false]
  · have one : slot m B kOk = 1 := by have := R.bit; omega
    simp [one]

end VG.Proof.RsaKeyGen.X86.Key
