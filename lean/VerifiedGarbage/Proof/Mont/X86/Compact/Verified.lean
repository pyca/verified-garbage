module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Mont.X86.Compact.Correct
import VerifiedGarbage.Proof.Mont.X86.Compact.ConstantTime
import VerifiedGarbage.Proof.Mont.X86.Compact.Satisfiable
/-! # Verified paired-word prepared Montgomery multiplication on i686 -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86

theorem verified : Verified target VG.Impl.Mont.X86.Compact.body (Proof.Rsa.Mont.mulContract abi 16) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Mont.X86.Compact
