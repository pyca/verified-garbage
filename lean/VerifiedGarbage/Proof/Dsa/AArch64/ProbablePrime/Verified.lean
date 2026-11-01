module

import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Correct
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.CT
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Depth

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

/-- Its frames: its own 272 bytes. -/
theorem testCode_depth (v : RoundImpl) (bits : Nat) : 16 * (testCode v bits).aarch64Depth ≤ stack := by
  have h := aarch64Depth_of_noFrames _ (test_noFrames v bits)
  simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

/-- The tests with the round implementation `v`, as parameter generation
calls them. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.PrimeTest where
  name bits := s!"vg_dsa_probable_prime_{(Impl.Dsa.AArch64.ProbablePrime.layout bits).bits}" ++ v.suffix
  code := testCode v
  verified _ hb := verified v hb
  depth := testCode_depth v

end VG.Proof.Dsa.AArch64.ProbablePrime
