module

public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MillerRabin.X86.Correct
import VerifiedGarbage.Proof.MillerRabin.X86.ConstantTime
import VerifiedGarbage.Proof.MillerRabin.X86.Satisfiable

/-! # Verified prepared fixed-window Miller–Rabin on baseline i686 -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem verified : Verified target (VG.Impl.MillerRabin.X86.code montName montCode)
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.MillerRabin.X86
