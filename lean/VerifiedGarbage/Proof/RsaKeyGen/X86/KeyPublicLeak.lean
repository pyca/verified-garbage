module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEncodedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
/-! # Equal shared observations give the exponent and retry equality used by native timing -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyStatusRetry.lean`, which only this module imported.
section

/-! # The shared encoded status releases exactly the numeric retry branch -/

section
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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem PublicInputs.exponentValue {s t : State} (P : PublicInputs s t) :
    inputExponent (callEnvironment s) s.mem = inputExponent (callEnvironment s) t.mem := by
  have H := P.exponent
  unfold callEBytes at H
  rw [← P.environment] at H
  exact congrArg Spec.Rsa.os2ip H

theorem PublicInputs.release {s t : State} (P : PublicInputs s t) (h : contract.pre s) :
    (Spec.RsaKeyGen.keyFromPrimes (32 * (callEnvironment s).n)
      (inputExponent (callEnvironment s) s.mem) (inputPrime (callEnvironment s) s.mem 2)
      (inputPrime (callEnvironment s) s.mem 3) = .inr ()) ↔
    (Spec.RsaKeyGen.keyFromPrimes (32 * (callEnvironment s).n)
      (inputExponent (callEnvironment s) s.mem) (inputPrime (callEnvironment s) t.mem 2)
      (inputPrime (callEnvironment s) t.mem 3) = .inr ()) := by
  have v := call_valid h
  have status := P.status
  unfold callKeyStatus at status
  rw [← P.environment] at status
  have right := status_retry_iff v t.mem
  rw [← P.exponentValue] at right
  have same : (Spec.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) s.mem) = 2) ↔
      (Spec.RsaKeyGen.keyStatus (encodedOperation (callEnvironment s) t.mem) = 2) := by rw [status]
  exact (status_retry_iff v s.mem).symm.trans (same.trans right)

end VG.Proof.RsaKeyGen.X86.Key
