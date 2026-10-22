module

public import VerifiedGarbage.Proof.MillerRabin.X86.Correct
public import VerifiedGarbage.Proof.MillerRabin.X86.ConstantTime
public import VerifiedGarbage.Proof.MillerRabin.X86.Satisfiable

/-! # The baseline i686 prepared Miller–Rabin round is verified -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem round_verified : Verified target code
    (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes) :=
  ⟨round_correct, round_constantTime, round_satisfiable⟩

end VG.Proof.MillerRabin.X86
