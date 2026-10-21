module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Install entry arguments one at a time, preserving previously initialized slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

def validSavedSlots (slots : List Nat) : Bool := slots.all fun d => d % 4 == 0 && decide (d + 4 ≤ 72)

theorem SavedFrame.install {s t : State} {values : Nat → BitVec 32} {slots : List Nat} {d : Nat}
    {rs : List Reg} (h : SavedFrame values slots s) (valid : validSavedSlots slots = true)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) (values d))
    (rest : Rest rs s t) : SavedFrame values (d :: slots) t := by
  refine ⟨by rw [rest.sp]; exact h.space.congr rest.wr, ?_⟩
  intro e he
  rw [rest.sp, memory]
  by_cases same : e = d
  · subst e
    exact Mem.readW_writeW_self32 _ _ _
  · have old : e ∈ slots := (List.mem_cons.mp he).resolve_left same
    have bounds := List.all_eq_true.mp valid e old
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at bounds
    have separate : (⟨State.addr (s.sp + BitVec.ofNat 32 e), 4⟩ : Region).Disjoint
        ⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ := by
      rw [VG.Arm.addr_add (by have := h.space.nowrap; omega), VG.Arm.addr_add (by have := h.space.nowrap; omega)]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [Mem.readW_writeW_sep (separate.sep (Region.contains_self _ 4) (Region.contains_self _ 4)) (by decide)]
    exact h.saved e old

end VG.Proof.Ffdh.Arm.ParameterCandidate
