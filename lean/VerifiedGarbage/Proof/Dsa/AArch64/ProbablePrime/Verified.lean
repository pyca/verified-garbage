module

import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Correct
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.CT
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend

/-! # `vg_dsa_probable_prime_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) (bits : Nat) : Prog isa :=
  Impl.Dsa.AArch64.ProbablePrime.code bits v.mont.mm v.kernel.run

theorem verified (v : RoundImpl) {bits : Nat} (hb : Supported bits) :
    Verified target (testCode v bits) (contract bits) :=
  ⟨correct v.mont v.kernel hb, code_ct v.mont v.kernel hb, satisfiable hb⟩

end VG.Proof.Dsa.AArch64.ProbablePrime
