module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa

/-! Exact memory effects of the four public phase-policy stores. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont

theorem phaseStore_word (m : Mem) (sp : BitVec 32) {d offset : Nat}
    (nowrap : sp.toNat + 72 ≤ 2 ^ 32) (fit : d + 4 ≤ 72) (offsetFit : offset + 4 ≤ 72)
    (separate : d = offset ∨ d + 4 ≤ offset ∨ offset + 4 ≤ d) (value : BitVec 32) :
    (m.writeW (State.addr (sp + BitVec.ofNat 32 offset)) value).readW
      (State.addr (sp + BitVec.ofNat 32 d)) 32 =
      if d = offset then value else m.readW (State.addr (sp + BitVec.ofNat 32 d)) 32 := by
  by_cases same : d = offset
  · subst d
    rw [Mem.readW_writeW_self32, ite_eq_left rfl]
  · have disjoint : (⟨State.addr (sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
        ⟨State.addr (sp + BitVec.ofNat 32 offset), 4⟩ := by
      rw [VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [Mem.readW_writeW_sep (disjoint.sep (Region.contains_self _ 4) (Region.contains_self _ 4))
      (by decide), ite_eq_right same]

theorem phaseMemory_word {s : State} {q : Bool} {bits d : Nat}
    (nowrap : s.sp.toNat + 72 ≤ 2 ^ 32) (fit : d + 4 ≤ 72) (aligned : d % 4 = 0) :
    (phaseMemory s q bits).readW (State.addr (s.sp + BitVec.ofNat 32 d)) 32 =
      if d = 56 then 0#32 else if d = 52 then BitVec.ofNat 32 (Spec.Ffdh.primeChecks (phaseBits q bits))
      else if d = 48 then BitVec.ofNat 32 ((phaseBits q bits + 7) / 8)
      else if d = 44 then BitVec.ofNat 32 (phaseBits q bits)
      else s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 d)) 32 := by
  unfold phaseMemory
  rw [phaseStore_word _ _ nowrap fit (by decide : 56 + 4 ≤ 72) (by omega)]
  rw [phaseStore_word _ _ nowrap fit (by decide : 52 + 4 ≤ 72) (by omega)]
  rw [phaseStore_word _ _ nowrap fit (by decide : 48 + 4 ≤ 72) (by omega)]
  rw [phaseStore_word _ _ nowrap fit (by decide : 44 + 4 ≤ 72) (by omega)]

theorem phaseMemory_frame {s : State} (q : Bool) (bits : Nat) (nowrap : s.sp.toNat + 72 ≤ 2 ^ 32) :
    Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem (phaseMemory s q bits) := by
  have contained (d : Nat) (lower : 44 ≤ d) (upper : d + 4 ≤ 60) :
      (⟨State.addr (s.sp + 44#32), 16⟩ : Region).Contains (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  unfold phaseMemory
  exact ((((Frame.refl _ _).writeW (by simp) _ (contained 44 (by decide) (by decide))).writeW
    (by simp) _ (contained 48 (by decide) (by decide))).writeW
    (by simp) _ (contained 52 (by decide) (by decide))).writeW
    (by simp) _ (contained 56 (by decide) (by decide))

end VG.Proof.Ffdh.Arm.ParameterCandidate
