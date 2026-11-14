module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.RequestBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.TerminalMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Rc2.PairMem

/-! ### `Ffdh.Arm.ParameterSearch.Terminal`, which only this module used -/

section

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

end

end


/-! Exact low and high halves after native terminal and refill writes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (lowWord lowWord_store highStore_low highStore_high highWord_store)

theorem terminalMem_low (m : Mem) (base : BitVec 32) (status j : Nat) (hj : j < 16) :
    lowWord (terminalMem m base status) base j =
      if j = 13 then BitVec.ofNat 32 status else if j = 0 ∨ j = 3 then 0 else lowWord m base j := by
  unfold terminalMem
  rw [lowWord_store (i := 13) _ _ _ (by decide) hj,
    highStore_low (i := 3) _ _ _ (by decide) hj,
    lowWord_store (i := 3) _ _ _ (by decide) hj,
    highStore_low (i := 0) _ _ _ (by decide) hj,
    lowWord_store (i := 0) _ _ _ (by decide) hj]
  by_cases h13 : j = 13
  · simp [h13]
  · by_cases h0 : j = 0
    · simp [h0]
    · by_cases h3 : j = 3 <;> simp [h13, h0, h3]

theorem terminalMem_high (m : Mem) (base : BitVec 32) (status j : Nat) (hj : j < 4) :
    (terminalMem m base status).readW (off (State.addr base) (8 * j + 4)) 32 =
      if j = 0 ∨ j = 3 then 0 else m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  unfold terminalMem
  rw [highWord_store (i := 13) _ _ _ (by decide) (by omega_using [hj]),
    highStore_high (i := 3) _ _ _ (by decide) (by omega_using [hj]),
    highWord_store (i := 3) _ _ _ (by decide) (by omega_using [hj]),
    highStore_high (i := 0) _ _ _ (by decide) (by omega_using [hj]),
    highWord_store (i := 0) _ _ _ (by decide) (by omega_using [hj])]
  by_cases h0 : j = 0 <;> by_cases h3 : j = 3 <;> simp [h0, h3]

theorem requestMem_low (m : Mem) (base : BitVec 32) (request j : Nat) (hj : j < 16) :
    lowWord (requestMem m base request) base j =
      if j = 13 then 0 else if j = 3 then BitVec.ofNat 32 request else lowWord m base j := by
  unfold requestMem
  rw [lowWord_store (i := 13) _ _ _ (by decide) hj,
    highStore_low (i := 3) _ _ _ (by decide) hj, lowWord_store (i := 3) _ _ _ (by decide) hj]
  rfl

theorem requestMem_high (m : Mem) (base : BitVec 32) (request j : Nat) (hj : j < 4) :
    (requestMem m base request).readW (off (State.addr base) (8 * j + 4)) 32 =
      if j = 3 then 0 else m.readW (off (State.addr base) (8 * j + 4)) 32 := by
  unfold requestMem
  rw [highWord_store (i := 13) _ _ _ (by decide) (by omega_using [hj]),
    highStore_high (i := 3) _ _ _ (by decide) (by omega_using [hj]),
    highWord_store (i := 3) _ _ _ (by decide) (by omega_using [hj])]
  rfl

theorem requestMem_frame (m : Mem) (base : BitVec 32) (request : Nat) :
    Frame [⟨State.addr base, 128⟩] m (requestMem m base request) := by
  unfold requestMem
  exact (((Frame.refl _ _).writeW (by simp) _ (VG.Offset.contains_base _ (by decide : 24 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (VG.Offset.contains_base _ (by decide : 28 + 4 ≤ 128) (by decide))).writeW
    (by simp) _ (VG.Offset.contains_base _ (by decide : 104 + 4 ≤ 128) (by decide))

theorem word_eq {m m' : Mem} {base : BitVec 32} {j : Nat}
    (low : lowWord m' base j = lowWord m base j)
    (high : m'.readW (off (State.addr base) (8 * j + 4)) 32 =
      m.readW (off (State.addr base) (8 * j + 4)) 32) :
    m'.readW (off (State.addr base) (8 * j)) 64 = m.readW (off (State.addr base) (8 * j)) 64 := by
  rw [VG.Proof.Rc2.Word32.read64_pair, VG.Proof.Rc2.Word32.read64_pair]
  have address : off (State.addr base) (8 * j) + BitVec.ofNat 64 4 = off (State.addr base) (8 * j + 4) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [address, high, show m'.readW (off (State.addr base) (8 * j)) 32 = _ from low]
  rfl

theorem terminalMem_word (m : Mem) (base : BitVec 32) (status j : Nat) (hj : j < 4) :
    (terminalMem m base status).readW (off (State.addr base) (8 * j)) 64 =
      if j = 0 ∨ j = 3 then 0 else m.readW (off (State.addr base) (8 * j)) 64 := by
  by_cases zero : j = 0 ∨ j = 3
  · rw [ite_eq_left zero]
    exact VG.Proof.Ffdh.Arm.KeySearch.packedWord _ _ _ 0 (by decide)
      (by rw [terminalMem_low _ _ _ _ (by omega_using [hj])]; simp [zero, show j ≠ 13 by omega_using [hj]])
      (by rw [terminalMem_high _ _ _ _ hj]; simp [zero])
  · rw [ite_eq_right zero]
    apply word_eq
    · rw [terminalMem_low _ _ _ _ (by omega_using [hj])]
      simp [zero, show j ≠ 13 by omega_using [hj]]
    · rw [terminalMem_high _ _ _ _ hj, ite_eq_right zero]

theorem requestMem_word (m : Mem) (base : BitVec 32) (request j : Nat) (hj : j < 4)
    (fit : request < 2 ^ 32) :
    (requestMem m base request).readW (off (State.addr base) (8 * j)) 64 =
      if j = 3 then BitVec.ofNat 64 request else m.readW (off (State.addr base) (8 * j)) 64 := by
  by_cases three : j = 3
  · rw [ite_eq_left three]
    exact VG.Proof.Ffdh.Arm.KeySearch.packedWord _ _ _ request fit
      (by rw [requestMem_low _ _ _ _ (by omega_using [hj])]; simp [three])
      (by rw [requestMem_high _ _ _ _ hj]; simp [three])
  · rw [ite_eq_right three]
    apply word_eq
    · rw [requestMem_low _ _ _ _ (by omega_using [hj])]
      simp [three, show j ≠ 13 by omega_using [hj]]
    · rw [requestMem_high _ _ _ _ hj, ite_eq_right three]

end VG.Proof.Ffdh.Arm.ParameterSearch
