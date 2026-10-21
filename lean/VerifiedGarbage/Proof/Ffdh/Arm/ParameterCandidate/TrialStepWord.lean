module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16Value
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialDigit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The exact accumulator, needed to relate public trial-division branch decisions. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm.TrialDivision16

def trialDigitWord (m : Mem) (endPtr : BitVec 32) (n : Nat) : BitVec 32 :=
  (m (State.addr (endPtr - 1))).setWidth 32 |||
    (if n = 1 then (0 : BitVec 32) else (m (State.addr (endPtr - 2))).setWidth 32 <<< 8)

theorem trialStepWord_ok (s : State) {n : Nat} (positive : 0 < n) (fits : n < 2 ^ 32)
    (count : s.gpr .r1 = BitVec.ofNat 32 n)
    (readLow : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 1)) 1)
    (readHigh : 1 < n → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 - 2)) 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep s fun t =>
      t.gpr .r2 = redcWord (trialDigitWord s.mem (s.gpr .r0) n) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 - BitVec.ofNat 32 (min 2 n) ∧
      t.gpr .r1 = BitVec.ofNat 32 (n - min 2 n) ∧ t.z = decide (n ≤ 2) ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r2, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep
  refine WP.seq (WP.mono (trialDigit_ok s positive fits count readLow readHigh) ?_)
  rintro u ⟨⟨ptr, cnt, word, mem⟩, rest⟩
  rw [WP.block_append_iff]
  refine WP.mono (redcWord_ok u) ?_
  rintro v ⟨⟨acc, memory⟩, kept⟩
  refine wp_cmp (op2_imm (by decide)) fun t flags zero => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, flags.mem.trans (memory.trans mem),
    (rest.mono (by simp)).trans ((kept.mono (by simp)).trans (flags.rest _))⟩
  · rw [flags.gpr, acc, word, rest.gpr .r2 (by simp), rest.gpr .r4 (by simp), rest.gpr .r3 (by simp)]
    rfl
  · rw [flags.gpr, kept.gpr .r0 (by simp), ptr]
  · rw [flags.gpr, kept.gpr .r1 (by simp), cnt]
  · rw [zero, kept.gpr .r1 (by simp), cnt]
    change (BitVec.ofNat 32 (n - min 2 n) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]
    change (BitVec.ofNat 32 (n - min 2 n) == (0 : BitVec 32)) = _
    rw [ofNat_beq_zero (by omega : n - min 2 n < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
