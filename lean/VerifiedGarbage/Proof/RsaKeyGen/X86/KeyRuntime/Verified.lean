module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyABI
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Correct
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ConstantTime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySatisfiable

/-! # Shared native key generation satisfies the existing API and timing contracts -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86

theorem verified : Verified target VG.Impl.RsaKeyGen.X86.KeyRuntime.code VG.Proof.RsaKeyGen.X86.Key.contract :=
  ⟨correct, constantTime, VG.Proof.RsaKeyGen.X86.Key.satisfiable⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
