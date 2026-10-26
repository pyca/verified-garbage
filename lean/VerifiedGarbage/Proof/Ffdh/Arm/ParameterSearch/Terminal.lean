module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Util.CompileInductive

/-! Terminal results clear both halves of the native attempt and request words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

def terminalMem (m : Mem) (base : BitVec 32) (status : Nat) : Mem :=
  ((((m.writeW (off (State.addr base) 0) (0#32)).writeW (off (State.addr base) 4) (0#32)).writeW
    (off (State.addr base) 24) (0#32)).writeW (off (State.addr base) 28) (0#32)).writeW
    (off (State.addr base) 104) (BitVec.ofNat 32 status)

theorem terminal_ok (s : State) {base : BitVec 32} {status : Nat}
    (h : Controller base s) (bound : status = 1 ∨ status = 3) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterSearch.terminal status)) s fun t =>
      t.mem = terminalMem s.mem base status ∧ Rest [.r10, .r11] s t := by
  refine withRest_all [.r10, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.terminal VG.Impl.Ffdh.Arm.ParameterSearch.stf terminalMem
  rcases bound with rfl | rfl <;>
    ffrun [controllerAddr h 0 (by decide), controllerAddr h 4 (by decide),
      controllerAddr h 24 (by decide), controllerAddr h 28 (by decide), controllerAddr h 104 (by decide),
      h.space.write (off := 0) (by decide), h.space.write (off := 4) (by decide),
      h.space.write (off := 24) (by decide), h.space.write (off := 28) (by decide),
      h.space.write (off := 104) (by decide)]
  all_goals rfl

theorem terminalMem_frame (m : Mem) (base : BitVec 32) (status : Nat) :
    Frame [⟨State.addr base, 128⟩] m (terminalMem m base status) := by
  unfold terminalMem
  exact (((((Frame.refl _ _).writeW (by simp) _ (Offset.contains_base _ (by decide : 0 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 4 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 24 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 28 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (Offset.contains_base _ (by decide : 104 + 4 ≤ 128) (by decide))

end VG.Proof.Ffdh.Arm.ParameterSearch
