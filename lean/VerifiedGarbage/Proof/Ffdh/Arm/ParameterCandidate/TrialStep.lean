module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialDigit
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Framework.Omega

/-! A candidate's byte pair calls the shared RSA reduction with unchanged
small-divisor and inverse registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

/-- The next least-significant digit, padded at an odd leading byte. -/
def trialDigitNat (m : Mem) (endPtr : BitVec 32) (n : Nat) : Nat :=
  (m (State.addr (endPtr - 1))).toNat +
    if n = 1 then 0 else 256 * (m (State.addr (endPtr - 2))).toNat

theorem trialStep_ok (s : State) {n acc divisor inverse : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1)
    (readHigh : 1 < n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 2)) 1)
    (accValue : s.gpr .r2 = BitVec.ofNat 32 acc) (accBound : acc < 2 * divisor)
    (divValue : s.gpr .r3 = BitVec.ofNat 32 divisor) (divBound : 3 ≤ divisor ∧ divisor < 8162)
    (invValue : (s.gpr .r4).toNat = inverse) (invCorrect : (divisor * inverse + 1) % 2 ^ 16 = 0) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep s fun t =>
      ∃ next, next < 2 * divisor ∧
        next * 2 ^ 16 % divisor = (trialDigitNat s.mem (s.gpr .r0) n + acc) % divisor ∧
        t.gpr .r2 = BitVec.ofNat 32 next ∧
        t.gpr .r0 = s.gpr .r0 - BitVec.ofNat 32 (min 2 n) ∧
        t.gpr .r1 = BitVec.ofNat 32 (n - min 2 n) ∧
        t.z = decide (n ≤ 2) ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr, cnt, word, mem⟩, rest⟩
  have digitValue : (u.gpr .r5).toNat = trialDigitNat s.mem (s.gpr .r0) n := by
    rw [word]
    unfold trialDigitNat
    by_cases last : n = 1
    · simp only [last, ite_true, show (0 : BitVec 32) = 0#32 from rfl,
        BitVec.or_zero, Nat.add_zero, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.mem (State.addr (s.gpr .r0 - 1))).isLt; omega)
    · rw [ite_eq_right last, ite_eq_right last, trialDigit_value]
  have digitBound : trialDigitNat s.mem (s.gpr .r0) n < 2 ^ 16 := by
    have lo := (s.mem (State.addr (s.gpr .r0 - 1))).isLt
    have hi := (s.mem (State.addr (s.gpr .r0 - 2))).isLt
    unfold trialDigitNat
    split <;> omega
  refine VG.Proof.Bignum.Arm.TrialDivision16.redc_ok digitValue digitBound
    ((rest.gpr .r2 (by simp)).trans accValue) accBound
    (by rw [rest.gpr .r4 (by simp)]; exact invValue)
    ((rest.gpr .r3 (by simp)).trans divValue) divBound invCorrect ?_
  intro v keep memory next bound congruence value
  refine wp_cmp (op2_imm (by decide)) fun t final flag => WP.block_nil ?_
  refine ⟨next, bound, congruence, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [final.gpr, value]
  · rw [final.gpr, keep.gpr .r0 (by simp), ptr]
  · rw [final.gpr, keep.gpr .r1 (by simp), cnt]
  · rw [flag, keep.gpr .r1 (by simp), cnt]
    change (BitVec.ofNat 32 (n - min 2 n) - (0 : BitVec 32) == (0 : BitVec 32)) = _
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.sub_zero]
    change (BitVec.ofNat 32 (n - min 2 n) == (0 : BitVec 32)) = _
    rw [ofNat_beq_zero (by omega : n - min 2 n < 2 ^ 32)]
    simp only [show n - min 2 n = 0 ↔ n ≤ 2 by omega]
  · rw [final.mem, memory, mem]
  · exact (rest.mono (by simp)).trans ((keep.mono (by simp)).trans (final.rest _))

end VG.Proof.Ffdh.Arm.ParameterCandidate
