module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Rejection advances the public tape and consumed count by precisely the candidate's usage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord writeLow)

def rejectFields (p : SearchParams) (used count : Nat) : List (Nat × BitVec 32) :=
  [(4, BitVec.ofNat 32 (used + count)), (9, p.c.tape + BitVec.ofNat 32 (used + count)),
    (10, BitVec.ofNat 32 (p.c.bytes.length - (used + count)))]

theorem rejectHead_ok {p : SearchParams} {used remaining count : Nat} {s : State}
    (h : SearchLive p used remaining s) (bound : count ≤ p.c.bytes.length - used)
    (consumed : lowWord s.mem p.control 14 = BitVec.ofNat 32 count) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.rejectHead) s fun t =>
      t.mem = writeLow s.mem p.control (rejectFields p used count) ∧ Rest [.r9, .r10, .r11, .r12] s t := by
  have usedValue := h.saved 4 (by simp [searchSlots])
  have sourceValue := h.saved 9 (by simp [searchSlots])
  have lengthValue := h.saved 10 (by simp [searchSlots])
  simp only [searchValues] at usedValue sourceValue lengthValue
  have countFit : count < 2 ^ 32 := by have := p.c.tapeCount; omega
  have countRoom : count ≤ p.c.bytes.length - used := bound
  have sum : BitVec.ofNat 32 used + BitVec.ofNat 32 count = BitVec.ofNat 32 (used + count) :=
    BitVec.ofNat_add_ofNat _ _
  have source : p.c.tape + BitVec.ofNat 32 used + BitVec.ofNat 32 count =
      p.c.tape + BitVec.ofNat 32 (used + count) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have length : BitVec.ofNat 32 (p.c.bytes.length - used) - BitVec.ofNat 32 count =
      BitVec.ofNat 32 (p.c.bytes.length - (used + count)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ countFit countRoom]
    congr 1
    omega
  refine withRest [.r9, .r10, .r11, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.rejectHead : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  have control := h.buffers.controller
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.rejectHead VG.Impl.Ffdh.Arm.ParameterSearch.ldf
    VG.Impl.Ffdh.Arm.ParameterSearch.stf lowWord at *
  unfold writeLow rejectFields
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [control.addr (by decide : 14 < 16), control.addr (by decide : 4 < 16),
    control.addr (by decide : 9 < 16), control.addr (by decide : 10 < 16),
    control.read (by decide : 14 < 16), control.read (by decide : 4 < 16),
    control.read (by decide : 9 < 16), control.read (by decide : 10 < 16),
    control.write (by decide : 4 < 16), control.write (by decide : 9 < 16),
    control.write (by decide : 10 < 16), consumed, usedValue, sourceValue, lengthValue, sum, source, length]

end VG.Proof.Ffdh.Arm.ParameterSearch
