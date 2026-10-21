module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialMath
import VerifiedGarbage.Proof.Framework.Omega

/-! A bounded initial carry lets the same RSA reducer test p and p-1 from the same bytes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private def loopRegs : List Reg := [.r0, .r1, .r2, .r5, .r6, .r7]

theorem trialLoop_from_ok (s : State) {n divisor inverse initial : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n) (read : TrialReadable s (s.gpr .r0) n)
    (acc : s.gpr .r2 = BitVec.ofNat 32 initial) (initialBound : initial < 2*divisor)
    (divValue : s.gpr .r3 = BitVec.ofNat 32 divisor) (divBound : 3 ≤ divisor ∧ divisor < 8162)
    (invValue : (s.gpr .r4).toNat = inverse) (invCorrect : (divisor * inverse + 1) % 2 ^ 16 = 0) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) s fun t =>
      ∃ next j, next < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * j) % divisor = (initial+trialValue s.mem (s.gpr .r0) n) % divisor ∧
        t.gpr .r1 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  let original := initial+trialValue s.mem (s.gpr .r0) n
  let inv := fun k t => ∃ j a, 0 < k ∧ k < 2 ^ 32 ∧
    TrialReadable t (t.gpr .r0) k ∧ t.gpr .r1 = BitVec.ofNat 32 k ∧
    a < 2 * divisor ∧ t.gpr .r2 = BitVec.ofNat 32 a ∧
    (a + trialValue t.mem (t.gpr .r0) k) * 2 ^ (16 * j) % divisor = original % divisor ∧
    t.mem = s.mem ∧ Rest loopRegs s t
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k u h
    obtain ⟨j, a, kp, kfit, readable, cnt, ab, av, cong, memory, rest⟩ := h
    refine WP.mono (trialStep_ok u kp kfit cnt (readable.low kp) (fun h => readable.high h)
      av ab ((rest.gpr .r3 (by simp [loopRegs])).trans divValue) divBound
      (by rw [rest.gpr .r4 (by simp [loopRegs])]; exact invValue) invCorrect) ?_
    rintro t ⟨b, bb, step, bv, ptr, cnt', flag, mem, keep⟩
    have congruence : (b + trialValue t.mem (t.gpr .r0) (k - min 2 k)) *
        2 ^ (16 * (j + 1)) % divisor = original % divisor := by
      rw [trialValue_step u.mem (u.gpr .r0) kp] at cong
      rw [mem, ptr]
      exact trialRemaining_congruence step cong
    have nextRead : TrialReadable t (t.gpr .r0) (k - min 2 k) := by
      rw [ptr]
      exact readable.advance keep (Nat.min_le_right 2 k)
    have kept : Rest loopRegs s t := rest.trans keep
    by_cases last : k ≤ 2
    · have remZero : k - min 2 k = 0 := by omega
      left
      refine ⟨?_, b, j + 1, bb, bv, ?_, ?_, mem.trans memory, kept⟩
      · change some (!t.z) = some false
        simp only [flag, last, decide_true, Bool.not_true]
      · simpa only [remZero, trialValue, Nat.add_zero] using congruence
      · rw [cnt', remZero]
        rfl
    · right
      refine ⟨?_, k - min 2 k, by omega, j + 1, b, by omega, by omega,
        nextRead, cnt', bb, bv, congruence, mem.trans memory, kept⟩
      change some (!t.z) = some true
      simp only [flag, last, decide_false, Bool.not_false]
  · refine ⟨0, initial, positive, fits, read, count, initialBound, acc, ?_, rfl, Rest.refl _ _⟩
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
      rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
