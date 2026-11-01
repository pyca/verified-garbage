module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Core
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessCountNext
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsFrame
import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame

/-! # RSA's test writes only the header and the arrays

Every range the prepared Miller–Rabin test writes ends at or before array
28, where DSA's probable-prime test keeps its candidate.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86

theorem test_ranges_before (g : Geometry) : ∀ r ∈ CandidateTest.ranges g, r.1 + r.2 ≤ g.array 28 := by
  simp only [CandidateTest.ranges, Prepare.ranges, PrepareHeader.ranges, Header.ranges, PreparedR2.ranges,
    PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, Constants.ranges, Exponent.preparedRanges,
    Exponent.ranges, MillerRabinLoop.ranges, WitnessChecks.ranges, WitnessStep.ranges, WitnessRound.ranges,
    WitnessMont.ranges, roundWrites, WitnessCount.ranges, WitnessCount.nextRanges,
    VG.Impl.RsaKeyGen.X86.Exponent.markerOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset,
    VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, VG.Proof.Mont.X86.accLen,
    VG.Impl.Mont.X86.words, VG.Impl.Bignum.X86.PublicContext.modulus]
  omega

theorem test_ranges_header (g : Geometry) : ∀ r ∈ CandidateTest.ranges g, r.1 + r.2 ≤ 28 ∨ 48 ≤ r.1 := by
  simp only [CandidateTest.ranges, Prepare.ranges, PrepareHeader.ranges, Header.ranges, PreparedR2.ranges,
    PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, Constants.ranges, Exponent.preparedRanges,
    Exponent.ranges, MillerRabinLoop.ranges, WitnessChecks.ranges, WitnessStep.ranges, WitnessRound.ranges,
    WitnessMont.ranges, roundWrites, WitnessCount.ranges, WitnessCount.nextRanges,
    VG.Impl.RsaKeyGen.X86.Exponent.markerOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset,
    VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset, VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset,
    VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, VG.Proof.Mont.X86.accLen,
    VG.Impl.Mont.X86.words, VG.Impl.Bignum.X86.PublicContext.modulus]
  omega

end VG.Proof.Dsa.X86.ProbablePrime
