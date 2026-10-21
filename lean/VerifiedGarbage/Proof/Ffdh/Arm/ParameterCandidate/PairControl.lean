module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! Advance the shared prime cursor and bounded count once for each pair of trials. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem pairAdvanceCount_ok {s : State} {count : Nat} (positive : 0 < count) (bound : count ≤ 1024)
    (saved : s.gpr .r11 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount)) s fun t =>
      (t.gpr .r10 = s.gpr .r10 + 4 ∧ t.gpr .r11 = BitVec.ofNat 32 (count - 1) ∧
        t.z = decide (count = 1) ∧ t.mem = s.mem) ∧ Rest [.r10, .r11] s t := by
  have subtract : BitVec.ofNat 32 count - (1 : BitVec 32) = BitVec.ofNat 32 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have zero : (BitVec.ofNat 32 (count - 1) == (0 : BitVec 32)) = decide (count = 1) := by
    rw [ofNat_beq_zero (by omega : count - 1 < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega)
  refine withRest [.r10, .r11] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount) : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount
  ffrun [List.cons_append, List.nil_append, saved, subtract, zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
