module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Read radix-2^16 digits from a big-endian octet buffer, including its
single leading octet when the buffer has an odd length. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialDigitHead trialDigitHigh trialDigit)

theorem trialDigitHead_ok (s : State)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1) :
    WP isa (.block trialDigitHead) s fun t =>
      (t.gpr .r0 = s.gpr .r0 - 1 ∧ t.gpr .r1 = s.gpr .r1 - 1 ∧
        t.gpr .r5 = (s.mem (State.addr (s.gpr .r0 - 1))).setWidth 32 ∧
        t.z = (s.gpr .r1 - 1 == 0) ∧ t.mem = s.mem) ∧ Rest [.r0, .r1, .r5] s t := by
  refine withRest_all [.r0, .r1, .r5] ?_ (by rfl) (by rfl)
  unfold trialDigitHead
  ffrun [BitVec.add_zero, read]

theorem trialDigitHigh_ok (s : State)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1) :
    WP isa (.block trialDigitHigh) s fun t =>
      (t.gpr .r0 = s.gpr .r0 - 1 ∧ t.gpr .r1 = s.gpr .r1 - 1 ∧
        t.gpr .r5 = s.gpr .r5 ||| ((s.mem (State.addr (s.gpr .r0 - 1))).setWidth 32 <<< 8) ∧
        t.mem = s.mem) ∧ Rest [.r0, .r1, .r5, .r7] s t := by
  refine withRest_all [.r0, .r1, .r5, .r7] ?_ (by rfl) (by rfl)
  unfold trialDigitHigh
  ffrun [BitVec.add_zero, read]


theorem trialDigit_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1)
    (readHigh : 1 < n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 2)) 1) :
    WP isa trialDigit s fun t =>
      (t.gpr .r0 = s.gpr .r0 - BitVec.ofNat 32 (min 2 n) ∧
        t.gpr .r1 = BitVec.ofNat 32 (n - min 2 n) ∧
        t.gpr .r5 = (s.mem (State.addr (s.gpr .r0 - 1))).setWidth 32 |||
          (if n = 1 then (0 : BitVec 32) else (s.mem (State.addr (s.gpr .r0 - 2))).setWidth 32 <<< 8) ∧
        t.mem = s.mem) ∧ Rest [.r0, .r1, .r5, .r7] s t := by
  unfold trialDigit
  refine WP.seq (WP.mono (trialDigitHead_ok s readLow) ?_)
  rintro u ⟨⟨ptr, cnt, digit, zero, mem⟩, rest⟩
  have sub : s.gpr .r1 - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [count]
    change BitVec.ofNat 32 n - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  have flag : u.z = decide (n = 1) := by
    rw [zero, sub, ofNat_beq_zero (by omega : n - 1 < 2 ^ 32)]
    simp only [show n - 1 = 0 ↔ n = 1 by omega]
  have ptr2 : u.gpr .r0 - 1 = s.gpr .r0 - 2 := by
    rw [ptr, BitVec.sub_sub]; rfl
  by_cases last : n = 1
  · refine WP.ite true (by change some u.z = some true; simp only [flag, last, decide_true]) ?_
      (by intro h; cases h)
    intro _
    refine WP.block_nil ⟨⟨?_, ?_, ?_, mem⟩, rest.mono (by simp)⟩
    · simpa [last] using ptr
    · simpa [last, count] using cnt
    · simpa [last] using digit
  · refine WP.ite false (by change some u.z = some false; simp only [flag, last, decide_false])
      (by intro h; cases h) ?_
    intro _
    refine WP.mono (trialDigitHigh_ok u (by rw [rest.rd, rest.wr, ptr2]; exact readHigh (by omega))) ?_
    rintro t ⟨⟨tptr, tcnt, tdigit, tmem⟩, trest⟩
    refine ⟨⟨?_, ?_, ?_, tmem.trans mem⟩, (rest.mono (by simp)).trans trest⟩
    · rw [tptr, ptr2, Nat.min_eq_left (by omega : 2 ≤ n)]; rfl
    · rw [tcnt, cnt, sub]
      change BitVec.ofNat 32 (n - 1) - BitVec.ofNat 32 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      congr 1
      omega
    · rw [tdigit, digit, ptr2, mem, ite_eq_right last]

/-- A byte pair is a bounded digit for RSA's shared reducer. -/
theorem trialDigit_value (low high : Byte) :
    ((low.setWidth 32) ||| ((high.setWidth 32) <<< 8)).toNat = low.toNat + 256 * high.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have lo := low.isLt
  have hi := high.isLt
  rw [Nat.mod_eq_of_lt (by omega : low.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : high.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : high.toNat * 2 ^ 8 < 2 ^ 32)]
  rw [Nat.or_comm, Nat.mul_comm high.toNat, ← Nat.two_pow_add_eq_or_of_lt lo high.toNat]
  omega

end VG.Proof.Ffdh.Arm.ParameterCandidate
