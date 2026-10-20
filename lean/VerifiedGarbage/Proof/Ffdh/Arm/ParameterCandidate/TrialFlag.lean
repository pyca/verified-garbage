module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! The bounded Montgomery remainder is divisible precisely at zero or
one copy of the divisor. Comparisons preserve all data registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem sub_beq_zero (x y : BitVec 32) : (x - y == (0 : BitVec 32)) = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  change x - y = 0#32 ↔ x = y
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem ofNat_beq_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a == BitVec.ofNat 32 b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro same
    have value := congrArg BitVec.toNat same
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using value
  · intro same
    rw [same]

theorem trialFlag_ok (s : State) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag s fun t =>
      t.z = ((s.gpr .r2 == (0 : BitVec 32)) || (s.gpr .r2 == s.gpr .r3)) ∧
        t.mem = s.mem ∧ Rest [] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u changed flag => WP.block_nil ?_)
  have zero : u.z = (s.gpr .r2 == (0 : BitVec 32)) := by rw [flag, sub_beq_zero]
  by_cases first : (s.gpr .r2 == (0 : BitVec 32)) = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, first]) ?_ (by intro h; cases h)
    intro _
    refine WP.block_nil ⟨?_, changed.mem, changed.rest _⟩
    rw [zero, first]
    rfl
  · have noFirst : (s.gpr .r2 == (0 : BitVec 32)) = false := by cases h : (s.gpr .r2 == (0 : BitVec 32)) <;> simp_all
    refine WP.ite false (by change some u.z = some false; rw [zero, noFirst]) (by intro h; cases h) ?_
    intro _
    refine wp_cmp (op2_reg _ _) fun t last flag' => WP.block_nil ⟨?_, last.mem.trans changed.mem,
      (changed.rest []).trans (last.rest [])⟩
    rw [flag', changed.gpr, sub_beq_zero, noFirst]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
