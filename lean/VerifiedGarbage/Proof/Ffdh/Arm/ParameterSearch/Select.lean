module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Compare
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The request's two unsigned comparisons select an exact maximum and minimum. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm

abbrev select := VG.Impl.Ffdh.Arm.ParameterSearch.select

theorem select_ok (maximum : Bool) (s : State) :
    WP isa (select maximum) s fun t =>
      (t.gpr .r9 = (if maximum then
        if (s.gpr .r9).toNat < (s.gpr .r10).toNat then s.gpr .r10 else s.gpr .r9
        else if (s.gpr .r9).toNat < (s.gpr .r10).toNat then s.gpr .r9 else s.gpr .r10) ∧
        t.mem = s.mem) ∧ Rest [.r9, .r11] s t := by
  unfold select VG.Impl.Ffdh.Arm.ParameterSearch.select
  refine WP.seq (WP.mono (less_ok s) fun u ⟨⟨flag, mem⟩, rest⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag]) ?_ ?_
  · intro yes
    have lt := of_decide_eq_true yes
    cases maximum
    · simp only [Bool.false_eq_true, ite_false, lt, ite_true]
      exact WP.block_nil ⟨⟨rest.gpr .r9 (by simp), mem⟩, rest.mono (by simp)⟩
    · simp only [ite_true, lt]
      have run : WP isa (.block [.mov .r9 (.reg .r10)]) u fun t =>
          (t.gpr .r9 = s.gpr .r10 ∧ t.mem = s.mem) ∧ Rest [.r9] u t := by
        refine withRest [.r9] ?_ (by
          intro r hr i hi
          simp only [instrs, List.mem_singleton] at hi
          subst i
          cases r <;> simp_all [clobbers, dstOf]) (by rfl)
        ffrun [rest.gpr .r10 (by simp), mem]
      exact WP.mono run fun _ ⟨data, changed⟩ =>
        ⟨data, (rest.mono (by simp)).trans (changed.mono (by simp))⟩
  · intro no
    have ge := of_decide_eq_false no
    cases maximum
    · simp only [Bool.false_eq_true, ite_false, ge]
      have run : WP isa (.block [.mov .r9 (.reg .r10)]) u fun t =>
          (t.gpr .r9 = s.gpr .r10 ∧ t.mem = s.mem) ∧ Rest [.r9] u t := by
        refine withRest [.r9] ?_ (by
          intro r hr i hi
          simp only [instrs, List.mem_singleton] at hi
          subst i
          cases r <;> simp_all [clobbers, dstOf]) (by rfl)
        ffrun [rest.gpr .r10 (by simp), mem]
      exact WP.mono run fun _ ⟨data, changed⟩ =>
        ⟨data, (rest.mono (by simp)).trans (changed.mono (by simp))⟩
    · simp only [ite_true, ge, ite_false]
      exact WP.block_nil ⟨⟨rest.gpr .r9 (by simp), mem⟩, rest.mono (by simp)⟩

theorem selectNat_ok (maximum : Bool) (s : State) {x y : Nat}
    (xFits : x < 2 ^ 32) (yFits : y < 2 ^ 32)
    (left : s.gpr .r9 = BitVec.ofNat 32 x) (right : s.gpr .r10 = BitVec.ofNat 32 y) :
    WP isa (select maximum) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 32 (if maximum then max x y else min x y) ∧ t.mem = s.mem) ∧
        Rest [.r9, .r11] s t := by
  refine WP.mono (select_ok maximum s) ?_
  rintro t ⟨⟨value, mem⟩, rest⟩
  refine ⟨⟨?_, mem⟩, rest⟩
  rw [left, right, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt xFits, Nat.mod_eq_of_lt yFits] at value
  cases maximum <;> by_cases lt : x < y
  · simpa only [Bool.false_eq_true, ite_false, lt, ite_true, Nat.min_eq_left (Nat.le_of_lt lt)] using value
  · simpa only [Bool.false_eq_true, ite_false, lt, Nat.min_eq_right (by omega : y ≤ x)] using value
  · simpa only [ite_true, lt, Nat.max_eq_right (Nat.le_of_lt lt)] using value
  · simpa only [ite_true, lt, ite_false, Nat.max_eq_left (by omega : y ≤ x)] using value

end VG.Proof.Ffdh.Arm.ParameterSearch
