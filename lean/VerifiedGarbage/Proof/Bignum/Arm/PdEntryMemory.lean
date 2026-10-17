module

public import VerifiedGarbage.Proof.Bignum.Arm.PdEntry
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Packed-key entry memory preserves every saved argument except the count slot -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem pdEntry_memory {s t : State} {base : BitVec 32}
    (mem : t.mem = ((s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base).writeW
      (off (State.addr s.sp) 12) (s.gpr .r1)) :
    t.mem.readW (State.addr s.sp) 32 = base ∧
      t.mem.readW (off (State.addr s.sp) 4) 32 = s.gpr .r0 ∧
      t.mem.readW (off (State.addr s.sp) 8) 32 = s.mem.readW (off (State.addr s.sp) 8) 32 ∧
      t.mem.readW (off (State.addr s.sp) 12) 32 = s.gpr .r1 ∧
      Outside (State.addr s.sp) 0 16 s.mem t.mem ∧ Frame [⟨State.addr s.sp, 16⟩] s.mem t.mem := by
  let u : State := {s with mem := (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base}
  have first := pcEntry_memory (s := s) (t := u) (base := base) rfl
  have last := writeW32_outside u.mem (State.addr s.sp) (d := 12) (s.gpr .r1) (by decide)
  have outside : Outside (State.addr s.sp) 0 16 s.mem t.mem := by
    rw [mem]
    exact (first.2.2.1.mono (by decide) (by decide)).trans (last.mono (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_, outside, ?_⟩
  · have keep := outside_read32 last (d := 0) (by decide) (by decide)
    simp only [off, BitVec.add_zero] at keep
    rw [mem, keep]; exact first.1
  · rw [mem, outside_read32 last (d := 4) (by decide) (by decide)]; exact first.2.1
  · rw [mem, outside_read32 last (d := 8) (by decide) (by decide)]
    exact outside_read32 first.2.2.1 (by decide) (by decide)
  · rw [mem, Mem.readW_writeW_self32]
  · intro a ha
    apply outside a
    have h := ha ⟨State.addr s.sp, 16⟩ (by simp)
    change ¬ ((a - State.addr s.sp).toNat + 1 ≤ 16) at h
    right
    change 16 ≤ (a - State.addr s.sp).toNat
    omega

theorem pdEntry_callee_saved {s t : State} {base : BitVec 32} {g : Reg → BitVec 32}
    (saved : Spill.Saved s.mem (State.addr s.sp) g pcCalleeSaved)
    (mem : t.mem = ((s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base).writeW
      (off (State.addr s.sp) 12) (s.gpr .r1)) :
    Spill.Saved t.mem (State.addr s.sp) g pcCalleeSaved := by
  have frame := (pdEntry_memory mem).2.2.2.2.2
  apply saved.frame (lo := 16) (hi := 56) (by decide) frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact Offset.disjoint_base _ (by decide) (by decide)
end VG.Proof.Bignum.Arm
