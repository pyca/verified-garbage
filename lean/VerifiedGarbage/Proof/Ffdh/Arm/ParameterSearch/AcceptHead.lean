module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Accepting a candidate records exactly its consumed entropy before clearing the policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem acceptHead_ok {p : SearchParams} {used remaining count : Nat} {s : State}
    (h : SearchLive p used remaining s)
    (consumed : lowWord s.mem p.control 14 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.acceptHead) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 32) (BitVec.ofNat 32 (used + count)) ∧
        Rest [.r9, .r10] s t := by
  have usedValue := h.saved 4 (by simp [searchSlots])
  simp only [searchValues] at usedValue
  refine withRest [.r9, .r10] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.acceptHead : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  have control := h.buffers.controller
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.acceptHead VG.Impl.Ffdh.Arm.ParameterSearch.ldf
    VG.Impl.Ffdh.Arm.ParameterSearch.stf lowWord at *
  ffrun [control.addr (by decide : 14 < 16), control.addr (by decide : 4 < 16),
    control.read (by decide : 14 < 16), control.read (by decide : 4 < 16),
    control.write (by decide : 4 < 16), consumed, usedValue, BitVec.ofNat_add_ofNat]

end VG.Proof.Ffdh.Arm.ParameterSearch
