module

import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Correct
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.CT
import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Satisfiable
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Safety
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend

/-! # `vg_dsa_probable_prime` on x86-64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code v.inlineMont.mm (Kernel.called v).run

theorem testCode_safe (v : RoundImpl) :
    VG.Proof.Dsa.X86_64.Generation.generationSafe (testCode v) :=
  code_safe _ _ v.inlineSafe (VG.Proof.Dsa.X86_64.Generation.roundCode_safe v)

theorem verified (v : RoundImpl) : Verified target (testCode v) contract :=
  ⟨correct v.inlineMont (Kernel.called v) (testCode_safe v).mx, code_ct _ _, satisfiable⟩

/-- The test with the round implementation `v`, as parameter generation
calls it. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.X86_64.Generation.PrimeTest where
  name := (Spec.Dsa.ProbablePrime.sizedApi Impl.Dsa.X86_64.ProbablePrime.layout
    Impl.Dsa.X86_64.ProbablePrime.sizes).name ++ v.suffix
  code := testCode v
  verified := verified v
  safe := testCode_safe v
  depth := code_depth _ _ (VG.Proof.Dsa.X86_64.Generation.inlineMul_depth v)
    (VG.Proof.Dsa.X86_64.Generation.roundCode_depth v)

end VG.Proof.Dsa.X86_64.ProbablePrime
