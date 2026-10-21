module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySatisfiable

/-! # Complete native RSA key generation has correctness, timing and satisfiability certificates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.Key.code contract :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.Key
