module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsFinish
import VerifiedGarbage.Proof.Framework.Block

/-! A table record either gives an exact match or advances to the next record. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem step_ok (s : State) {table src : BitVec 32} {k : Nat} {dom : List Byte}
    {g : Group} {gs : List Group} (source : Source src k dom s) (record : RecordAt table g s)
    (cursor : Cursor table src k dom (g :: gs) s) (kfit : k < 2 ^ 32) (fit : gs.length < 2 ^ 32) :
    WP isa step s fun t => t.mem = s.mem ∧
      (if g.len = k ∧ dom = g.domain.take dom.length then
        t.gpr .r11 = BitVec.ofNat 32 g.bits ∧ t.gpr .r7 = 0 ∧ t.z = true else
        t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * g.len) ∧
          t.gpr .r7 = BitVec.ofNat 32 gs.length ∧ t.z = decide (gs.length = 0)) ∧
      Rest clobbers s t := by
  rw [step, WP.seq_iff]
  refine WP.mono (header_ok s record cursor.ptr cursor.width kfit) ?_
  rintro u ⟨⟨ptrU, sizeU, capU, oneU, zeroU, memU⟩, restU⟩
  rw [WP.seq_iff]
  have choose : WP isa (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) u fun v =>
      (v.gpr .r2 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧ v.mem = u.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r12, .lr] u v := by
    refine WP.ite (decide (g.len = k)) (by simp only [eval, zeroU]) ?_ ?_
    · intro yes
      have same := of_decide_eq_true yes
      refine WP.mono (compare_ok u (source.after memU restU) (record.after memU restU) same
        ((restU.gpr .r9 (by simp)).trans cursor.source) ptrU
        ((restU.gpr .r10 (by simp)).trans cursor.length)) ?_
      rintro v ⟨equal, mem, rest⟩
      exact ⟨by simpa only [same, true_and] using equal, mem, rest⟩
    · intro no
      have different := of_decide_eq_false no
      refine WP.block_nil ⟨?_, rfl, Rest.refl _ _⟩
      rw [oneU]
      simp only [show (1 : BitVec 32) ≠ 0 by decide, false_iff]
      exact fun h => different h.1
  refine WP.mono choose ?_
  rintro v ⟨equal, memV, restV⟩
  refine WP.mono (finish_ok v equal
    ((restV.gpr .r4 (by simp)).trans ptrU) ((restV.gpr .r5 (by simp)).trans sizeU)
    ((restV.gpr .r11 (by simp)).trans capU)
    ((restV.gpr .r7 (by simp)).trans ((restU.gpr .r7 (by simp)).trans cursor.count)) fit) ?_
  rintro t ⟨memT, result, restT⟩
  exact ⟨memT.trans (memV.trans memU), result,
    (restU.mono (by simp [clobbers])).trans
      ((restV.mono (by simp [clobbers])).trans (restT.mono (by simp [clobbers])))⟩

end VG.Proof.Ffdh.Arm.VettedGroups
