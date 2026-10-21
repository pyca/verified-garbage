module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry

/-! # The shared encoded status releases exactly the numeric retry branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG

theorem status_retry_iff {E : Environment} (v : E.Valid) (m : Mem) :
    Spec.RsaKeyGen.keyStatus (encodedOperation E m) = 2 ↔
      Spec.RsaKeyGen.keyFromPrimes (32 * E.n) (inputExponent E m) (inputPrime E m 2) (inputPrime E m 3) = .inr () := by
  have widths := v.widths
  have bits : 16 * E.primeLength = 32 * E.n := by omega
  unfold encodedOperation Spec.RsaKeyGen.keyOp inputExponent inputPrime
  rw [bits]
  generalize result : Spec.RsaKeyGen.keyFromPrimes (32 * E.n)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) = value
  cases value with
  | inl answer => cases answer <;> simp [Spec.RsaKeyGen.keyStatus]
  | inr u => cases u; simp [Spec.RsaKeyGen.keyStatus]

end VG.Proof.RsaKeyGen.X86.Key
