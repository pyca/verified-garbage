module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.FieldMemory
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! The internal continue status preserves every externally persistent live search field. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord writeLow lowWord_store)

theorem againBlock_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block [.mov .r11 (.imm 4), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 104) (4#32) ∧ Rest [.r11] s t := by
  refine withRest_all [.r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
  ffrun [h.addr (by decide : 13 < 16), h.write (by decide : 13 < 16)]
  rfl

theorem status_word (m : Mem) (base : BitVec 32) (value : BitVec 32) {j : Nat}
    (hj : j < 13) :
    (m.writeW (off (State.addr base) 104) value).readW (off (State.addr base) (8 * j)) 64 =
      m.readW (off (State.addr base) (8 * j)) 64 := by
  have word := fields_word m base [(13, value)] (by simp) (j := j) (by omega) (by simp; omega)
  exact word

theorem SearchLive.again {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa (.block [.mov .r11 (.imm 4), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r11 13]) s fun t =>
      (SearchLive p used remaining t ∧ lowWord t.mem p.control 13 = 4#32) ∧ Rest [.r11] s t := by
  refine WP.mono (againBlock_ok s h.buffers.controller) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 104 + 4 ≤ 128) (by decide))
  refine ⟨⟨?_, ?_⟩, rest⟩
  · refine SearchLive.after_control (nextUsed := used) (nextRemaining := remaining)
      h (by decide) frame rest h.usedBound h.remainingBound ?_ ?_ ?_ ?_
    · have word := status_word s.mem p.control 4#32 (j := 0) (by decide)
      have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
      rw [show 8 * 0 = 0 from rfl, address] at word
      rw [mem, word]
      exact h.counter
    · rw [mem, status_word _ _ _ (j := 1) (by decide)]
      exact h.width
    · rw [mem, status_word _ _ _ (j := 2) (by decide)]
      exact h.entropy
    · intro j member
      have bounds : j < 16 ∧ j ≠ 13 := by
        simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      rw [mem, lowWord_store (i := 13) _ _ _ (by decide) bounds.1, ite_eq_right bounds.2]
      exact h.saved j member
  · rw [mem, lowWord_store (i := 13) _ _ _ (by decide) (by decide)]
    rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
