module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialLoopFrom
import VerifiedGarbage.Proof.Framework.Omega

/-! The original zero-carry trial loop delegates to the shared bounded-carry proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem trialLoop_ok (s : State) {n divisor inverse : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (acc : s.gpr .r2 = 0)
    (divValue : s.gpr .r3 = BitVec.ofNat 32 divisor) (divBound : 3 ≤ divisor ∧ divisor < 8162)
    (invValue : (s.gpr .r4).toNat = inverse) (invCorrect : (divisor * inverse + 1) % 2 ^ 16 = 0) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      ∃ next j, next < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * j) % divisor = trialValue s.mem (s.gpr .r0) n % divisor ∧
        t.gpr .r1 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  simpa only [Nat.zero_add] using trialLoop_from_ok s (initial:=0) positive fits count read
    (by simpa using acc) (by have := divBound.1; omega) divValue divBound invValue invCorrect

end VG.Proof.Ffdh.Arm.ParameterCandidate
