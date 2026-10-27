module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Correct
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.CT
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Satisfiable
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Safety
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode

/-! # `vg_dsa_probable_prime_{bits}` on x86-64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) (bits : Nat) : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code bits v.inlineMont.mm (Kernel.called v).run

theorem testCode_safe (v : RoundImpl) (bits : Nat) :
    VG.Proof.Dsa.X86_64.Generation.generationSafe (testCode v bits) :=
  code_safe _ _ v.inlineSafe (VG.Proof.Dsa.X86_64.Generation.roundCode_safe v) bits

theorem verified (v : RoundImpl) {bits : Nat} (hb : Supported bits) :
    Verified target (testCode v bits) (contract bits) :=
  ⟨correct v.inlineMont (Kernel.called v) hb (testCode_safe v bits).mx, code_ct _ _ hb, satisfiable hb⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
