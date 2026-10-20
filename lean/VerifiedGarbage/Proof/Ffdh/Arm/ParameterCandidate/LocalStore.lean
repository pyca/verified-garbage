module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Update one saved native policy word while retaining the other arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_store {s t : State} {values : Nat → BitVec 32} {slots : List Nat}
    {offset : Nat} {value : BitVec 32} {rs : List Reg} (h : SavedFrame values slots s)
    (fit : offset + 4 ≤ 72) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (separate : ∀ d ∈ slots, d ≠ offset → d + 4 ≤ offset ∨ offset + 4 ≤ d)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 offset)) value)
    (rest : Rest rs s t) :
    SavedFrame (fun d => if d = offset then value else values d) slots t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]
    exact h.space.congr rest.wr
  · intro d hd
    rw [rest.sp, memory]
    by_cases same : d = offset
    · subst d
      rw [Mem.readW_writeW_self32, ite_eq_left rfl]
    · have disjoint : (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
          ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
        rw [VG.Arm.addr_add (by have := h.space.nowrap; have := bounds d hd; omega),
          VG.Arm.addr_add (by have := h.space.nowrap; omega)]
        exact Offset.disjoint _ (separate d hd same) (by have := bounds d hd; omega) (by omega)
      rw [Mem.readW_writeW_sep (disjoint.sep (Region.contains_self _ 4) (Region.contains_self _ 4)) (by decide),
        ite_eq_right same]
      exact h.saved d hd

end VG.Proof.Ffdh.Arm.ParameterCandidate
