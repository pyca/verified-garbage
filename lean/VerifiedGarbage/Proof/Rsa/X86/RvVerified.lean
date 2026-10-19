module

public import VerifiedGarbage.Proof.Rsa.X86.RvOperationTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvSatisfiable

/-! # Complete i686 certificate for RSA prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Recover

theorem verified : Verified target code (Spec.Rsa.recoverPrimesContract abi 20) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.Recover
