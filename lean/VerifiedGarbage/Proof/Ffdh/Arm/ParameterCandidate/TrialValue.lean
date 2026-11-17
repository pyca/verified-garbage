module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.ParameterCandidate.TrialDigit`, which this module and modules that import it used -/

section

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
    rw [zero, sub, ofNat_beq_zero (by omega_using [fits] : n - 1 < 2 ^ 32)]
    simp only [show n - 1 = 0 ↔ n = 1 by omega_using [positive]]
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
    refine WP.mono (trialDigitHigh_ok u (by rw [rest.rd, rest.wr, ptr2]; exact readHigh (by omega_using [positive, last]))) ?_
    rintro t ⟨⟨tptr, tcnt, tdigit, tmem⟩, trest⟩
    refine ⟨⟨?_, ?_, ?_, tmem.trans mem⟩, (rest.mono (by simp)).trans trest⟩
    · rw [tptr, ptr2, Nat.min_eq_left (by omega_using [positive, last] : 2 ≤ n)]; rfl
    · rw [tcnt, cnt, sub]
      change BitVec.ofNat 32 (n - 1) - BitVec.ofNat 32 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [positive, last])]
      congr 1
      omega_using []
    · rw [tdigit, digit, ptr2, mem, ite_eq_right last]

/-- A byte pair is a bounded digit for RSA's shared reducer. -/
theorem trialDigit_value (low high : Byte) :
    ((low.setWidth 32) ||| ((high.setWidth 32) <<< 8)).toNat = low.toNat + 256 * high.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have lo := low.isLt
  have hi := high.isLt
  rw [Nat.mod_eq_of_lt (by omega_using [] : low.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [] : high.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [] : high.toNat * 2 ^ 8 < 2 ^ 32)]
  rw [Nat.or_comm, Nat.mul_comm high.toNat, ← Nat.two_pow_add_eq_or_of_lt lo high.toNat]
  omega_using []

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.TrialStep`, which this module and modules that import it used -/

section

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
      exact Nat.mod_eq_of_lt (by have := (s.mem (State.addr (s.gpr .r0 - 1))).isLt; omega_using [])
    · rw [ite_eq_right last, ite_eq_right last, trialDigit_value]
  have digitBound : trialDigitNat s.mem (s.gpr .r0) n < 2 ^ 16 := by
    have lo := (s.mem (State.addr (s.gpr .r0 - 1))).isLt
    have hi := (s.mem (State.addr (s.gpr .r0 - 2))).isLt
    unfold trialDigitNat
    split <;> omega_using []
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
    rw [ofNat_beq_zero (by omega_using [fits] : n - min 2 n < 2 ^ 32)]
    simp only [show n - min 2 n = 0 ↔ n ≤ 2 by omega_using []]
  · rw [final.mem, memory, mem]
  · exact (rest.mono (by simp)).trans ((keep.mono (by simp)).trans (final.rest _))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! The remaining big-endian input, grouped by the same byte pairs as RSA's
radix-2^16 reducer. The final odd octet is a zero-padded leading digit. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

def trialValue (m : Mem) (endPtr : BitVec 32) : Nat → Nat
  | 0 => 0
  | 1 => trialDigitNat m endPtr 1
  | n + 2 => trialDigitNat m endPtr (n + 2) + 2 ^ 16 * trialValue m (endPtr - 2) n

theorem trialValue_step (m : Mem) (endPtr : BitVec 32) {n : Nat} (positive : 0 < n) :
    trialValue m endPtr n = trialDigitNat m endPtr n +
      2 ^ 16 * trialValue m (endPtr - BitVec.ofNat 32 (min 2 n)) (n - min 2 n) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => simp [trialValue]
    | succ n =>
      rw [Nat.min_eq_left (by omega_using [] : 2 ≤ n + 1 + 1)]
      simp only [show n + 1 + 1 - 2 = n by omega_using []]
      rfl

/-- Readability of the n bytes immediately preceding a native end pointer. -/
def TrialReadable (s : State) (endPtr : BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (endPtr - BitVec.ofNat 32 (i + 1))) 1

theorem TrialReadable.low {s : State} {endPtr : BitVec 32} {n : Nat}
    (h : TrialReadable s endPtr n) (positive : 0 < n) :
    InRegions (s.rd ++ s.wr) (State.addr (endPtr - 1)) 1 := h 0 positive

theorem TrialReadable.high {s : State} {endPtr : BitVec 32} {n : Nat}
    (h : TrialReadable s endPtr n) (more : 1 < n) :
    InRegions (s.rd ++ s.wr) (State.addr (endPtr - 2)) 1 := h 1 more

theorem TrialReadable.advance {s t : State} {endPtr : BitVec 32} {n c : Nat} {rs : List Reg}
    (h : TrialReadable s endPtr n) (rest : Rest rs s t) (bound : c ≤ n) :
    TrialReadable t (endPtr - BitVec.ofNat 32 c) (n - c) := by
  intro i hi
  rw [rest.rd, rest.wr, BitVec.sub_sub, ← BitVec.ofNat_add]
  have offset : c + (i + 1) = c + i + 1 := by omega
  rw [offset]
  exact h (c + i) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
