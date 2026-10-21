module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStatusRetry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs

/-! # Equal shared observations give the exponent and retry equality used by native timing -/

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
